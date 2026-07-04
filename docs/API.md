
# Spectral Holography API Reference

This document describes the C-compatible FFI (Foreign Function Interface) for the Isotropic Spectral Holography (ISH) library.

## Data Structures

### `ISHContext`
An opaque structure holding the cryptographic context (keys, reference salt, field parameters).
```c
typedef struct ISHContext ISHContext;
```

## Context Management

### `ish_create`
Creates a raw ISH context from explicit parameters.
**Warning**: Only for testing or advanced usage. Use password-based creation for standard security.

```c
ISHContext* ish_create(uint64_t seed, double x, double y, double z);
```
- `seed`: 64-bit seed for key derivation (Weak).
- `x, y, z`: 3D coordinates of the secret key location.
- **Returns**: Pointer to context, or NULL on failure.

### `ish_create_with_password`
Creates a secure ISH context from a password using Argon2id KDF.
This function generates a random salt and derives the key location and reference salt.

```c
ISHContext* ish_create_with_password(const char* password);
```
- `password`: Null-terminated string.
- **Returns**: Pointer to context.

### `ish_create_with_salt`
Creates a context using a password and a previously generated KDF salt (PHC string).
Required for decryption to ensure the same key is derived.

```c
ISHContext* ish_create_with_salt(const char* password, const char* salt_phc);
```
- `salt_phc`: The PHC-formatted string containing the salt and Argon2 parameters (stored in the encrypted file header).

### `ish_destroy`
Frees the memory associated with an ISH context.

```c
void ish_destroy(ISHContext* ctx);
```

## File Encryption / Decryption

### `ish_encrypt_file`
Encrypts a file using Standard ISH Mode (8x expansion).
Appends HMAC-SHA256 for integrity.

```c
int32_t ish_encrypt_file(ISHContext* ctx, const char* input_path, const char* output_path);
```
- **Returns**: 0 on success, negative error code on failure.

### `ish_decrypt_file`
Decrypts a file encrypted with Standard ISH Mode.
Verifies HMAC-SHA256 before processing.

```c
int32_t ish_decrypt_file(ISHContext* ctx, const char* input_path, const char* output_path);
```
- **Returns**: 0 on success, -100 on integrity failure.

### `ish_encrypt_file_z1`
Encrypts a file using **Z1 Compression Mode** (2x expansion).
Packs 4 bytes into one `f64` delta.

```c
int32_t ish_encrypt_file_z1(ISHContext* ctx, const char* input_path, const char* output_path);
```

### `ish_decrypt_file_z1`
Decrypts a file encrypted with Z1 Mode.

```c
int32_t ish_decrypt_file_z1(ISHContext* ctx, const char* input_path, const char* output_path);
```

## Buffer Operations

### `ish_ciphertext_len`
Calculates the expected ciphertext size for a given plaintext length (Standard Mode).

```c
size_t ish_ciphertext_len(size_t plaintext_len);
```

### `ish_encrypt` / `ish_decrypt` (Raw Buffers)
**Note**: These operate on in-memory buffers. For large data, use file APIs or chunk processing.

```c
void ish_encrypt(ISHContext* ctx, const uint8_t* input, uint8_t* output, size_t len);
int32_t ish_decrypt(ISHContext* ctx, const uint8_t* input, uint8_t* output, size_t len);
```

## Utilities

### `ish_free_string`
Frees a string allocated by the library (e.g., if any API returns a char*).

```c
void ish_free_string(char* s);
```
