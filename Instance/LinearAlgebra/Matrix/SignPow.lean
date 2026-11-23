module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Integer power and scoped integer power for real square matrices

`Matrix.signPow A s` is the integer power of `A : Matrix (Fin n) (Fin n) ℝ`: `1` for `s = 0`,
`A * ⋯ * A` (`s` factors) for `s > 0`, and `A⁻¹ * ⋯ * A⁻¹` (`-s` factors) for `s < 0`. This is
the matrix analogue of `Tensor.MatPow` (`Def/LinearAlgebra/Matrix/Matpow.lean`), which writes the
product out with `Tensor.matProd`; for matrices the monoid power `A ^ n` is that same product.

The instance is scoped and activates only under `open scoped Matrix`. Mathlib's
`Matrix.instDivInvMonoid` (`Mathlib.LinearAlgebra.Matrix.ZPow`) already provides a global
`HPow (Matrix n' n' R) ℤ (Matrix n' n' R)` in files that import it; a global instance here would
shadow it.
-/

@[expose] public section

namespace Matrix

/--
Integer power: `0 ↦ 1`, `s > 0 ↦ A ^ s`, `s < 0 ↦ A⁻¹ ^ (-s)`.

Mirrors `Tensor.MatPow`: the positive case is `s` copies of `A` and the negative case is `-s`
copies of `A⁻¹`.
-/
noncomputable def signPow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : ℤ) :
    Matrix (Fin n) (Fin n) ℝ :=
  if 0 ≤ s then A ^ s.toNat else A⁻¹ ^ (-s).toNat

/-- `A ^ s` for `s : ℤ` is the integer power `Matrix.signPow A s`. Scoped: active only under
`open scoped Matrix`. -/
noncomputable scoped instance instHPowSign {n : ℕ} :
    HPow (Matrix (Fin n) (Fin n) ℝ) ℤ (Matrix (Fin n) (Fin n) ℝ) :=
  ⟨signPow⟩

end Matrix
