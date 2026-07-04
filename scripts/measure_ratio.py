import ctypes
import os
import random

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

def run_ratio_test(dll_path=None):
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

    # Define necessary FFI signatures
    try:
        lib.ish_create_with_password.argtypes = [ctypes.c_char_p]
        lib.ish_create_with_password.restype = ctypes.c_void_p
        
        lib.ish_encrypt_file.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
        lib.ish_encrypt_file.restype = ctypes.c_int32
        
        lib.ish_encrypt_file_z1.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
        lib.ish_encrypt_file_z1.restype = ctypes.c_int32
        
        lib.ish_destroy.argtypes = [ctypes.c_void_p]
        lib.ish_destroy.restype = None
    except AttributeError:
        print("Warning: Required functions not found in DLL")
        return

    # Create Context
    password = b"TestPassword"
    ctx = lib.ish_create_with_password(password)
    if not ctx:
        print("Error: Failed to create ISH context")
        return

    print("\n=== Plaintext vs Ciphertext Volume Ratio Test ===")
    print(f"{'Size (B)':<10} | {'Std Size':<12} | {'Std Ratio':<10} | {'Z1 Size':<12} | {'Z1 Ratio':<10}")
    print("-" * 65)

    test_sizes = [100, 1024, 10240, 102400, 1024*1024] # 100B, 1KB, 10KB, 100KB, 1MB
    
    for size in test_sizes:
        in_file = f"temp_in_{size}.bin"
        out_file = f"temp_out_{size}.ish"
        out_file_z1 = f"temp_out_{size}.ishz"
        
        # Create random input file
        with open(in_file, "wb") as f:
            f.write(os.urandom(size))
            
        # Encrypt Std
        in_path = in_file.encode('utf-8')
        out_path = out_file.encode('utf-8')
        res = lib.ish_encrypt_file(ctx, in_path, out_path)
        
        std_size = 0
        std_ratio = 0.0
        if res == 0:
            std_size = os.path.getsize(out_file)
            std_ratio = std_size / size
            
        # Encrypt Z1
        out_path_z1 = out_file_z1.encode('utf-8')
        res_z1 = lib.ish_encrypt_file_z1(ctx, in_path, out_path_z1)
        
        z1_size = 0
        z1_ratio = 0.0
        if res_z1 == 0:
            z1_size = os.path.getsize(out_file_z1)
            z1_ratio = z1_size / size
            
        print(f"{size:<10} | {std_size:<12} | {std_ratio:<10.4f} | {z1_size:<12} | {z1_ratio:<10.4f}")
            
        # Cleanup temp files
        if os.path.exists(in_file): os.remove(in_file)
        if os.path.exists(out_file): os.remove(out_file)
        if os.path.exists(out_file_z1): os.remove(out_file_z1)

    lib.ish_destroy(ctx)
    print("-" * 65)
    print("Test Completed.")

if __name__ == "__main__":
    import sys
    dll_path = sys.argv[1] if len(sys.argv) > 1 else None
    run_ratio_test(dll_path)
