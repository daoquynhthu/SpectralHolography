# ISH 数学安全性分析报告 (ISH Mathematical Security Analysis)

## 1. 已识别漏洞与修复 (Identified Vulnerabilities & Fixes)

### 1.1 密文方差泄露 (Ciphertext Variance Leakage) [已修复]
- **问题描述**: 原始 ISH 算法中，由于 `delta = -p_target * val_a - val_b` 的线性关系，当 `p_target` 为常数（如明文全 0 或全 255）时，密文 `delta` 的方差直接反映了 `val_a` 和 `val_b` 的方差。对于 `p_target=0`，方差较小；对于 `p_target=255`，方差极大（~65000倍）。攻击者可通过观察密文方差推断明文的大致内容。
- **验证**: `tests/variance_test.rs` 显示原始方差比高达 62000。
- **修复**: 在加密前引入流密码白化层 `p_target = byte ^ mask`，其中 `mask` 是由位置相关的伪随机数生成器（PRNG）产生的。这使得 `p_target` 在统计上均匀分布，消除了明文相关的方差特征。
- **结果**: 修复后 `variance_test` 通过，方差比接近 1.0。

## 2. 潜在安全隐患 (Potential Security Risks)

### 2.1 坐标生成种子强度不足 (Insufficient Coordinate Seed Strength) [已修复]
- **问题描述**: 原始实现中每个数据块的采样坐标 `(x, y)` 仅由一个 64 位的 `seed` 决定。虽然 `seed` 本身来源于 256 位密钥，但攻击者只需穷举 $2^{64}$ 种可能的 `seed` 值，即可复原所有坐标。一旦坐标已知，攻击者可计算公开场 `val_a`，进而利用已知明文攻击（KPA）解出秘密场 `val_b`，导致全面破解。
- **风险等级**: 高 (High)。$2^{64}$ 计算量虽大但在国家级攻击者能力范围内。
- **修复**: 
  - 引入了 `derive_chunk_seed` 函数，使用 SHA-256 将 IV、密钥位置、参考盐值（Ref Salt）和 MAC 密钥混合，生成 256 位的种子。
  - 将坐标生成器升级为 `ChaCha20Rng`，直接使用 256 位种子初始化。
  - 每个数据块（Chunk）的加密/解密现在都使用独立的 256 位种子，彻底消除了 $2^{64}$ 穷举漏洞。
- **结果**: 种子空间扩展至 256 位，抗暴力破解能力达到现代加密标准。

### 2.2 线性关系利用 (Linearity Exploitation)
- **问题描述**: ISH 核心方程是线性的。虽然引入了非线性的坐标映射 `(x, y)`，但如果坐标被固定或预测，线性方程易于求解。
- **缓解**: 
  - 必须确保坐标生成的伪随机性不可预测且不可重现（依赖于强密钥）。
  - 通过上述 PRNG 升级（ChaCha20 + 256-bit Seed），坐标序列现在具有密码学强度的伪随机性，攻击者无法在不知道密钥的情况下预测坐标。
  - 此外，每个字节的坐标都包含随机抖动（Jitter），进一步增加了预测难度。

### 2.3 密钥派生 (Key Derivation)
- **现状**: 使用 Argon2id 进行密码哈希，参数为默认配置。这符合当前最佳实践，能有效抵抗 GPU/ASIC 暴力破解。
- **验证**: `tests/weak_kdf_collision.rs` 验证了 KDF 的抗碰撞性和计算成本（防暴力破解）。
- **建议**: 保持现状，确保盐值（Salt）的随机性和长度（已满足）。

## 3. 改进计划 (Improvement Plan)

1. **升级 PRNG**: [已完成] 废弃 SplitMix64，全面采用 `ChaCha20` 作为坐标生成器。
2. **代码重构**: [已完成] 所有文件加密/解密函数已更新为使用 `derive_chunk_seed` 和并行 `ChaCha20` 生成。
3. **完整性检查**: [已完成] 文件格式已包含 HMAC-SHA256 完整性校验，防止密文延展性攻击（Malleability Attack）。
