/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean -/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Def.NumberTheory.Padics.PontryaginDual
/-!
# Algebraic p-adic Pontryagin duals

This file defines the `ℤ_p`-linear dual `Hom(·, ℚ_p / ℤ_p)` and its
contragredient group action. No topology or continuity condition is imposed.
-/


namespace MetaMathlibExt

/-- The contragredient distributive group action on the p-adic Pontryagin dual. -/
noncomputable instance instContragredientDistribMulAction (p : ℕ) [Fact p.Prime] (G A : Type*)
    [Group G] [AddCommGroup A] [Module ℤ_[p] A] [DistribMulAction G A] [SMulCommClass G ℤ_[p] A] :
    DistribMulAction G (PadicPontryaginDual p A) where
  smul g φ := contragredientSMul p G A g φ
  smul_zero g := by
    ext a
    change (0 : PadicPontryaginDual p A) (g⁻¹ • a) = 0
    rfl
  smul_add g φ ψ := by
    ext a
    change (φ + ψ) (g⁻¹ • a) = φ (g⁻¹ • a) + ψ (g⁻¹ • a)
    rfl
  one_smul φ := by
    ext a
    change φ ((1 : G)⁻¹ • a) = φ a
    simp
  mul_smul g h φ := by
    ext a
    change φ ((g * h)⁻¹ • a) = φ (h⁻¹ • g⁻¹ • a)
    rw [mul_inv_rev, mul_smul]

end MetaMathlibExt
