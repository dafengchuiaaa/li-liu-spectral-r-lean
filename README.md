# Discrete lemmas for the Li–Liu spectral hypothesis R audit

Seven Lean 4 theorems check finite arithmetic steps used in Yilin Liu’s *Failure of the Li–Liu spectral hypothesis R under Dirichlet GRH* (v1, 21 November 2026). The file uses Lean’s bundled library and has no Mathlib or Lake dependencies. All seven lemmas are unconditional. The analytic estimates, the Hardy-space matrix entry and the implication from Dirichlet GRH to failure of R remain outside the formalization. [Preprint and source](https://hexagonmath.org/2611.00788v1)

中文说明：本仓库将反驳论文中可独立复用的七个离散步骤写成 Lean 4 定理。机器核验覆盖换元、奇偶性、支撑内的同余、最大公因数和有限集合计数。Buchstab 渐近、算子范数下界及反驳论文的主定理仍需解析证明。

## Run the proof checker

With Lean 4.12.0 on your PATH, or Elan installed to read the included toolchain pin, run these commands from the repository directory.

```sh
lean --version
lean -o LiLiuAudit.olean LiLiuAudit.lean
```

A successful second command produces the compiled module. To use these theorems in another project on the same toolchain, copy [LiLiuAudit.lean](LiLiuAudit.lean) into the project's Lean source root and add `import LiLiuAudit`. The declarations live in the `LiLiuAudit` namespace.

## What is proved

| Declaration | Statement and use |
| --- | --- |
| `shiftCoordinates` | The integer substitutions `h = m − a` and `t = a + m` have the stated inverses, and `m − a = 2m − t` in the second coordinates. Used in §3. |
| `parityOfShifts` | The signed coordinates `a − m` and `a + m` agree modulo 2. |
| `oddCentre` | Both coordinates are even when the centre and summation variable are odd. For even sieve modulus this excludes odd centres in §3. |
| `supportResidues` | With `10m < N` and `4N < 5n < 6N`, divisibility of `n − m` or `n + m` by `N` selects precisely `n = N + m` or `n = N − m`, respectively. This checks the support step of Lemma 2.1. |
| `unitOnBothShifts` | For `m ≤ N`, both `gcd N (N + m)` and `gcd N (N − m)` equal `gcd m N`. |
| `thresholdBudget` | For a finite list with scores bounded above by a cap, the total score is at most the cut times the number below the cut plus the cap times the number at or above it. Scores may be negative. |
| `deletionLoss` | Filtering any list by a Boolean predicate and its complement partitions its length exactly. With a duplicate-free list this counts surviving and discarded integers. |

## Related work

- Jiamin Li and Jianya Liu define the operator and spectral hypotheses used in the preprint. [Original paper](https://mrc.sdu.edu.cn/english/info/1018/1514.htm)
- For a Lean development of the original conditional Goldbach results under the spectral assumptions, see [subfish-zhou/conditional-goldbach-lean](https://github.com/subfish-zhou/conditional-goldbach-lean).
- A separate written comparison examines the bilinear matrix entry of the November 21 preprint. [mxym/math, LiLiuRParallelCheck.md](https://github.com/mxym/math/blob/27b494e172a289104e92623ebf69c7e22f521caa/research/theory-2026-11-20/strong-goldbach/LiLiuRParallelCheck.md)

## License

The code is available under the [MIT License](LICENSE).
