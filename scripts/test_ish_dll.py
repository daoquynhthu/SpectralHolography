import ctypes
import os
import sys

def find_dll():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    candidates = [
        os.path.join(script_dir, "..", "target", "release", "spectral_holography.dll"),
        os.path.join(script_dir, "target", "release", "spectral_holography.dll"),
        os.path.join(script_dir, "..", "target", "debug", "spectral_holography.dll"),
        os.path.join(script_dir, "target", "debug", "spectral_holography.dll"),
    ]
    for p in candidates:
        if os.path.exists(p):
            return os.path.normpath(p)
    return None

def test_dll(dll_path=None):
    if dll_path is None:
        dll_path = find_dll()
    if dll_path is None:
        print("Error: Could not find spectral_holography.dll. Pass path as argument or build first.")
        return
    if not os.path.exists(dll_path):
        print(f"Error: DLL not found at {dll_path}")
        return

    try:
        lib = ctypes.CDLL(dll_path)
    except Exception as e:
        print(f"Error loading DLL: {e}")
        return

    # Define argument types and return types
    lib.ish_create.argtypes = [ctypes.c_uint64, ctypes.c_double, ctypes.c_double]
    lib.ish_create.restype = ctypes.c_void_p

    try:
        lib.ish_create_with_password.argtypes = [ctypes.c_char_p]
        lib.ish_create_with_password.restype = ctypes.c_void_p
    except AttributeError:
        print("Warning: ish_create_with_password not found")

    lib.ish_ciphertext_len.argtypes = [ctypes.c_size_t]
    lib.ish_ciphertext_len.restype = ctypes.c_size_t

    lib.ish_encrypt.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_ubyte), ctypes.POINTER(ctypes.c_ubyte), ctypes.c_size_t]
    lib.ish_encrypt.restype = None

    lib.ish_decrypt.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_ubyte), ctypes.POINTER(ctypes.c_ubyte), ctypes.c_size_t]
    lib.ish_decrypt.restype = None

    lib.ish_destroy.argtypes = [ctypes.c_void_p]
    lib.ish_destroy.restype = None
    
    # File I/O interfaces
    try:
        lib.ish_encrypt_file.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
        lib.ish_encrypt_file.restype = ctypes.c_int32
        
        lib.ish_decrypt_file.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
        lib.ish_decrypt_file.restype = ctypes.c_int32
    except AttributeError:
        print("Warning: File I/O functions not found in DLL (maybe old build?)")

    # Test Data
    seed = 12345 
    x = 10.0
    y = 20.0
    input_data = b"Hello, World! ISH Encryption Test"
    input_len = len(input_data)
    
    print(f"Input data: {input_data}")

    # Create Context
    print("Creating ISH Context...")
    ctx = lib.ish_create(seed, x, y)
    if not ctx:
        print("Error: Failed to create ISH context")
        return

    # --- Memory Test ---
    print("\n--- Memory Buffer Test ---")
    buffer_len = lib.ish_ciphertext_len(input_len)
    encrypted_buffer = (ctypes.c_ubyte * buffer_len)()
    input_buffer = (ctypes.c_ubyte * input_len).from_buffer_copy(input_data)
    
    lib.ish_encrypt(ctx, input_buffer, encrypted_buffer, input_len)
    
    # Inspect
    iv_bytes = bytes(encrypted_buffer[0:8])
    count_bytes = bytes(encrypted_buffer[8:16])
    iv = int.from_bytes(iv_bytes, byteorder='little')
    count = int.from_bytes(count_bytes, byteorder='little')
    print(f"IV: {iv}")
    print(f"Valid Blocks: {count}")

    # Decrypt
    decrypted_buffer = (ctypes.c_ubyte * input_len)()
    lib.ish_decrypt(ctx, encrypted_buffer, decrypted_buffer, buffer_len)
    decrypted_bytes = bytes(decrypted_buffer)
    print(f"Decrypted: {decrypted_bytes}")
    
    if decrypted_bytes == input_data:
        print("MEMORY SUCCESS")
    else:
        print("MEMORY FAILURE")

    # --- File I/O Test ---
    print("\n--- File I/O Test ---")
    test_file_in = "test_plain.txt"
    test_file_enc = "test_encrypted.ish"
    test_file_dec = "test_decrypted.txt"
    
    with open(test_file_in, "wb") as f:
        f.write(input_data * 10) # Write a bit more data
        
    print(f"Created {test_file_in} ({os.path.getsize(test_file_in)} bytes)")
    
    # Encrypt File
    in_path = test_file_in.encode('utf-8')
    out_path = test_file_enc.encode('utf-8')
    
    res = lib.ish_encrypt_file(ctx, in_path, out_path)
    if res == 0:
        print(f"File Encryption Success. Output size: {os.path.getsize(test_file_enc)} bytes")
    else:
        print(f"File Encryption Failed with code: {res}")
        
    # Decrypt File
    dec_path = test_file_dec.encode('utf-8')
    res = lib.ish_decrypt_file(ctx, out_path, dec_path)
    if res == 0:
        print(f"File Decryption Success.")
        with open(test_file_dec, "rb") as f:
            content = f.read()
        if content == input_data * 10:
             print("FILE SUCCESS: Content matches.")
        else:
             print("FILE FAILURE: Content mismatch.")
    else:
        print(f"File Decryption Failed with code: {res}")

    # Cleanup
    lib.ish_destroy(ctx)
    
    # Remove temp files
    # os.remove(test_file_in)
    # os.remove(test_file_enc)
    # os.remove(test_file_dec)

    # --- Password Test ---
    print("\n--- Password API Test ---")
    password = b"MySecretPassword123"
    print(f"Using Password: {password}")
    
    ctx_pass = lib.ish_create_with_password(password)
    if not ctx_pass:
        print("Error: Failed to create context from password")
        return
        
    # Encrypt small buffer
    test_msg = b"Password Protected Data"
    t_len = len(test_msg)
    out_len = lib.ish_ciphertext_len(t_len)
    
    enc_buf = (ctypes.c_ubyte * out_len)()
    in_buf = (ctypes.c_ubyte * t_len).from_buffer_copy(test_msg)
    
    lib.ish_encrypt(ctx_pass, in_buf, enc_buf, t_len)
    print(f"Encrypted {t_len} bytes with password context.")
    
    # Decrypt
    dec_buf = (ctypes.c_ubyte * t_len)()
    lib.ish_decrypt(ctx_pass, enc_buf, dec_buf, out_len)
    
    if bytes(dec_buf) == test_msg:
        print("PASSWORD SUCCESS: Data recovered.")
    else:
        print("PASSWORD FAILURE: Data mismatch.")
        
    lib.ish_destroy(ctx_pass)

if __name__ == "__main__":
    import sys
    dll_path = sys.argv[1] if len(sys.argv) > 1 else None
    test_dll(dll_path)
