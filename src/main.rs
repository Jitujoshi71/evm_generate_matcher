use bip32::{DerivationPath, XPrv};
use bip39::{Language, Mnemonic};
use crossbeam_channel::{bounded, Receiver, Sender};
use k256::elliptic_curve::sec1::ToEncodedPoint;
use memmap2::Mmap;
use rand::{CryptoRng, RngCore};
use sha3::{Digest, Keccak256};
use std::collections::HashSet;
use std::error::Error;
use std::fs::{self, File, OpenOptions};
use std::hash::Hasher;
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};
use sysinfo::System;
use twox_hash::XxHash64;
use zeroize::Zeroizing;

type AppError = Box<dyn Error + Send + Sync + 'static>;
type AppResult<T> = Result<T, AppError>;

// ==================================================
// Configuration & Constants
// ==================================================
const WORDLIST_FILE: &str = "word.txt";
const EVM_DERIVATION_PATH: &str = "m/44'/60'/0'/0/0";

// Bloom Filter Constants
const TOTAL_BITS: u64 = 76_884_517_000;
const NUM_HASHES: u64 = 50;
const BLOOM_FILE_BYTES: u64 = ((TOTAL_BITS + 63) / 64) * 8;

const BLOOM_PATH: &str = "evm_10_15.bloom";
const MATCHED_OUTPUT_CSV: &str = "matched_output.csv";

const WORKER_CHECK_BATCH_SIZE: usize = 2048;
const CHANNEL_CAPACITY: usize = 10_000;
const OUTPUT_BUFFER_SIZE: usize = 8 * 1024 * 1024;

// ==================================================
// Data Structures
// ==================================================
#[derive(Clone)]
struct WalletRecord {
    mnemonic: String,
    address: String,
}

struct HardwareInfo {
    cpu_name: String,
    logical_cores: usize,
    physical_cores: usize,
    total_memory_gb: f64,
}

// ==================================================
// Hardware & Wordlist Setup
// ==================================================
fn scan_system_hardware() -> HardwareInfo {
    let mut system = System::new_all();
    system.refresh_all();

    let logical_cores = system.cpus().len().max(1);

    let physical_cores = system
        .physical_core_count()
        .unwrap_or(logical_cores)
        .max(1);

    let cpu_name = system
        .cpus()
        .first()
        .map(|cpu| cpu.brand().trim().to_owned())
        .filter(|name| !name.is_empty())
        .unwrap_or_else(|| "Unknown CPU".to_owned());

    let total_memory_gb = system.total_memory() as f64 / (1024.0 * 1024.0 * 1024.0);

    HardwareInfo {
        cpu_name,
        logical_cores,
        physical_cores,
        total_memory_gb,
    }
}

fn load_and_validate_wordlist(path: &Path) -> AppResult<Vec<String>> {
    let content = fs::read_to_string(path).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!("Could not read word list '{}': {}", path.display(), error),
        )
    })?;

    let words: Vec<String> = content
        .lines()
        .map(|line| line.trim().trim_start_matches('\u{feff}').to_owned())
        .filter(|word| !word.is_empty())
        .collect();

    if words.len() != 2048 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("word.txt must contain exactly 2048 words; found {}", words.len()),
        )
        .into());
    }

    let unique_words: HashSet<&str> = words.iter().map(String::as_str).collect();

    if unique_words.len() != 2048 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "word.txt contains duplicate words",
        )
        .into());
    }

    let official_words = Language::English.word_list();

    for (index, file_word) in words.iter().enumerate() {
        let expected_word = official_words[index];

        if file_word.as_str() != expected_word {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "word.txt does not match official BIP-39 list at index {}. Expected {:?}, found {:?}",
                    index, expected_word, file_word
                ),
            )
            .into());
        }
    }

    Ok(words)
}

// ==================================================
// EVM Derivation Logic
// ==================================================
fn generate_evm_wallet<R>(
    derivation_path: &DerivationPath,
    wordlist: &[String],
    rng: &mut R,
) -> AppResult<WalletRecord>
where
    R: RngCore + CryptoRng,
{
    if wordlist.len() != 2048 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("Expected 2048 BIP-39 words, found {}", wordlist.len()),
        )
        .into());
    }

    loop {
        let mut mnemonic_phrase = String::with_capacity(128);

        for word_position in 0..12 {
            let word_index = (rng.next_u32() & 0x07ff) as usize;

            if word_position > 0 {
                mnemonic_phrase.push(' ');
            }

            mnemonic_phrase.push_str(wordlist[word_index].as_str());
        }

        let validated_mnemonic = match Mnemonic::parse_in(Language::English, &mnemonic_phrase) {
            Ok(mnemonic) => mnemonic,
            Err(_) => continue,
        };

        let seed = Zeroizing::new(validated_mnemonic.to_seed(""));
        let address = derive_evm_address(&*seed, derivation_path)?;

        return Ok(WalletRecord {
            mnemonic: mnemonic_phrase,
            address,
        });
    }
}

fn derive_evm_address(
    seed: &[u8; 64],
    derivation_path: &DerivationPath,
) -> AppResult<String> {
    let child_xprv = XPrv::derive_from_path(seed, derivation_path)?;
    let extended_public_key = child_xprv.public_key();
    let public_key = extended_public_key.public_key();
    let encoded_point = public_key.to_encoded_point(false);
    let encoded_bytes = encoded_point.as_bytes();

    if encoded_bytes.len() != 65 || encoded_bytes[0] != 0x04 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Invalid uncompressed secp256k1 public key",
        )
        .into());
    }

    let public_key_bytes = &encoded_bytes[1..];
    let hash = Keccak256::digest(public_key_bytes);

    Ok(to_checksum_address(&hash[12..]))
}

fn to_checksum_address(address_bytes: &[u8]) -> String {
    debug_assert_eq!(address_bytes.len(), 20);

    let lowercase_address = hex::encode(address_bytes);
    let address_hash = Keccak256::digest(lowercase_address.as_bytes());

    let mut checksummed = String::with_capacity(42);
    checksummed.push_str("0x");

    for (index, character) in lowercase_address.chars().enumerate() {
        if character.is_ascii_digit() {
            checksummed.push(character);
            continue;
        }

        let hash_byte = address_hash[index / 2];
        let hash_nibble = if index % 2 == 0 {
            (hash_byte >> 4) & 0x0f
        } else {
            hash_byte & 0x0f
        };

        if hash_nibble >= 8 {
            checksummed.push(character.to_ascii_uppercase());
        } else {
            checksummed.push(character);
        }
    }

    checksummed
}

// ==================================================
// Bloom Filter Logic
// ==================================================
#[inline(always)]
fn get_two_hashes(data: &[u8]) -> (u64, u64) {
    let mut h1 = XxHash64::with_seed(0);
    h1.write(data);
    let hash1 = h1.finish();

    let mut h2 = XxHash64::with_seed(hash1);
    h2.write(data);
    let hash2 = h2.finish();

    (hash1, hash2)
}

#[inline(always)]
fn bloom_contains(mmap: &[u8], raw_address: &[u8]) -> bool {
    debug_assert_eq!(raw_address.len(), 42);

    let mut lowercase_address = [0u8; 42];
    lowercase_address.copy_from_slice(raw_address);
    lowercase_address.make_ascii_lowercase();

    let (h1, h2) = get_two_hashes(&lowercase_address);

    for i in 0..NUM_HASHES {
        let bit_idx = h1.wrapping_add(i.wrapping_mul(h2)) % TOTAL_BITS;
        let byte_idx = (bit_idx / 8) as usize;
        let bit_mask = 1u8 << (bit_idx % 8);

        if (mmap[byte_idx] & bit_mask) == 0 {
            return false;
        }
    }

    true
}

// ==================================================
// File & Output Helpers
// ==================================================
fn output_file_needs_header(path: &Path) -> AppResult<bool> {
    let metadata = match fs::metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(true),
        Err(error) => return Err(error.into()),
    };

    if metadata.len() == 0 {
        return Ok(true);
    }

    let file = File::open(path)?;
    let mut reader = BufReader::new(file);
    let mut first_line = String::new();
    reader.read_line(&mut first_line)?;

    let header = first_line.trim_end_matches(['\r', '\n']);
    if header != "mnemonic,address" {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Unexpected CSV header {:?}; expected \"mnemonic,address\"", header),
        )
        .into());
    }

    Ok(false)
}

#[cfg(unix)]
fn open_secure_output_file(path: &Path) -> AppResult<File> {
    use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};

    let file = OpenOptions::new()
        .create(true)
        .append(true)
        .mode(0o600)
        .open(path)?;

    fs::set_permissions(path, fs::Permissions::from_mode(0o600))?;
    Ok(file)
}

#[cfg(not(unix))]
fn open_secure_output_file(path: &Path) -> AppResult<File> {
    let file = OpenOptions::new().create(true).append(true).open(path)?;
    Ok(file)
}

fn matched_writer_thread(
    receiver: Receiver<WalletRecord>,
    csv_path: &Path,
    matched_counter: &AtomicU64,
) -> AppResult<u64> {
    let needs_header = output_file_needs_header(csv_path)?;
    let file = open_secure_output_file(csv_path)?;
    let mut writer = BufWriter::with_capacity(OUTPUT_BUFFER_SIZE, file);

    if needs_header {
        writer.write_all(b"mnemonic,address\n")?;
    }

    let mut current_matches = 0_u64;

    while let Ok(record) = receiver.recv() {
        let line = format!("\"{}\",{}\n", record.mnemonic, record.address);
        writer.write_all(line.as_bytes())?;
        current_matches += 1;
        matched_counter.fetch_add(1, Ordering::Relaxed);
        writer.flush()?;
    }

    writer.flush()?;
    Ok(current_matches)
}

// ==================================================
// Worker Loop: Generate -> Bloom Check -> Send
// ==================================================
fn worker_loop(
    derivation_path: &DerivationPath,
    wordlist: &[String],
    mmap: &[u8],
    running: &AtomicBool,
    matched_sender: &Sender<WalletRecord>,
    scanned_counter: &AtomicU64,
) -> AppResult<()> {
    let mut rng = rand::thread_rng();
    let mut local_scanned = 0_u64;

    while running.load(Ordering::Relaxed) {
        let wallet = generate_evm_wallet(derivation_path, wordlist, &mut rng)?;
        local_scanned += 1;

        if bloom_contains(mmap, wallet.address.as_bytes()) {
            let _ = matched_sender.send(wallet);
        }

        if local_scanned >= WORKER_CHECK_BATCH_SIZE as u64 {
            scanned_counter.fetch_add(local_scanned, Ordering::Relaxed);
            local_scanned = 0;
        }
    }

    if local_scanned > 0 {
        scanned_counter.fetch_add(local_scanned, Ordering::Relaxed);
    }

    Ok(())
}

// ==================================================
// Main Pipeline
// ==================================================
fn main() -> AppResult<()> {
    println!("========================================================");
    println!("        EVM GENERATOR & BLOOM MATCHER PIPELINE          ");
    println!("========================================================");

    let hardware = scan_system_hardware();
    println!("CPU Model         : {}", hardware.cpu_name);
    println!("Physical Cores    : {}", hardware.physical_cores);
    println!("Logical Threads   : {}", hardware.logical_cores);
    println!("System Memory     : {:.2} GB", hardware.total_memory_gb);
    println!("Word List         : {}", WORDLIST_FILE);
    println!("Derivation Path   : {}", EVM_DERIVATION_PATH);
    println!("Bloom Filter File : {}", BLOOM_PATH);
    println!("Matched Output    : {}", MATCHED_OUTPUT_CSV);
    println!("========================================================");
    println!();

    println!("Loading and validating {}...", WORDLIST_FILE);
    let wordlist = Arc::new(load_and_validate_wordlist(Path::new(WORDLIST_FILE))?);
    println!("Word list loaded: {} BIP-39 words verified.", wordlist.len());

    println!("Loading Bloom filter: {}", BLOOM_PATH);
    let bloom_file = File::open(BLOOM_PATH).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!("Bloom filter open nahi hui '{}': {}", BLOOM_PATH, error),
        )
    })?;

    let actual_bloom_size = bloom_file.metadata()?.len();
    if actual_bloom_size != BLOOM_FILE_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "Invalid Bloom file size. Expected {} bytes, got {} bytes",
                BLOOM_FILE_BYTES, actual_bloom_size
            ),
        )
        .into());
    }

    let mmap = unsafe { Mmap::map(&bloom_file)? };
    let mmap = Arc::new(mmap);
    println!("Bloom filter loaded: {} bytes mapped in memory.", actual_bloom_size);

    let derivation_path = Arc::new(DerivationPath::from_str(EVM_DERIVATION_PATH)?);
    let running = Arc::new(AtomicBool::new(true));
    let scanned_counter = Arc::new(AtomicU64::new(0));
    let matched_counter = Arc::new(AtomicU64::new(0));

    {
        let running = Arc::clone(&running);
        ctrlc::set_handler(move || {
            running.store(false, Ordering::SeqCst);
        })?;
    }

    let allocated_workers = thread::available_parallelism()
        .map(|v| v.get())
        .unwrap_or(hardware.logical_cores)
        .max(1);

    println!("Allocated {} parallel generator threads.", allocated_workers);

    let (sender, receiver) = bounded::<WalletRecord>(CHANNEL_CAPACITY);
    let output_path = PathBuf::from(MATCHED_OUTPUT_CSV);

    let writer_handle = {
        let matched_counter = Arc::clone(&matched_counter);
        thread::spawn(move || matched_writer_thread(receiver, &output_path, &matched_counter))
    };

    let mut worker_handles = Vec::with_capacity(allocated_workers);

    for _ in 0..allocated_workers {
        let path = Arc::clone(&derivation_path);
        let words = Arc::clone(&wordlist);
        let mmap_ref = Arc::clone(&mmap);
        let run = Arc::clone(&running);
        let snd = sender.clone();
        let scn_cnt = Arc::clone(&scanned_counter);

        worker_handles.push(thread::spawn(move || {
            let result = worker_loop(&path, words.as_slice(), &mmap_ref, &run, &snd, &scn_cnt);
            if result.is_err() {
                run.store(false, Ordering::SeqCst);
            }
            result
        }));
    }

    drop(sender);

    let start = Instant::now();
    println!();
    println!("Pipeline running... Press Ctrl+C to safely exit.");
    println!();

    while running.load(Ordering::Relaxed) {
        thread::sleep(Duration::from_secs(1));

        let scanned = scanned_counter.load(Ordering::Relaxed);
        let matched = matched_counter.load(Ordering::Relaxed);
        let elapsed = start.elapsed().as_secs_f64();
        let speed = if elapsed > 0.0 {
            scanned as f64 / elapsed
        } else {
            0.0
        };

        print!(
            "\rGenerated/Scanned: {:>12} | Matches: {:>6} | Time: {:>5.1}s | Speed: {:>8.0} wallets/s",
            scanned, matched, elapsed, speed
        );
        io::stdout().flush()?;
    }

    println!("\n\nShutting down threads and flushing files...");

    for handle in worker_handles {
        let _ = handle.join();
    }

    let total_matches = writer_handle
        .join()
        .map_err(|_| io::Error::other("Writer thread panicked"))??;

    let total_time = start.elapsed().as_secs_f64();
    let total_scanned = scanned_counter.load(Ordering::Relaxed);
    let avg_speed = if total_time > 0.0 {
        total_scanned as f64 / total_time
    } else {
        0.0
    };

    println!("--------------------------------------------------");
    println!("Execution Summary");
    println!("Total Scanned : {}", total_scanned);
    println!("Total Matched : {}", total_matches);
    println!("Elapsed Time  : {:.2} s", total_time);
    println!("Average Speed : {:.0} wallets/s", avg_speed);
    println!("Output Saved  : {}", MATCHED_OUTPUT_CSV);
    println!("--------------------------------------------------");

    Ok(())
}
