/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean -/

import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Algebraic p-adic Pontryagin duals

This file defines the `ℤ_p`-linear dual `Hom(·, ℚ_p / ℤ_p)` and its
contragredient group action. No topology or continuity condition is imposed.
-/

namespace MetaMathlibExt

/-- The additive quotient `ℚ_p / ℤ_p`, represented using the canonical algebra map. -/
noncomputable abbrev PadicQuotientInt (p : ℕ) [Fact p.Prime] :=
  ℚ_[p] ⧸ LinearMap.range (Algebra.linearMap ℤ_[p] ℚ_[p])

/-- The algebraic `ℤ_p`-linear Pontryagin dual with values in `ℚ_p / ℤ_p`. -/
noncomputable abbrev PadicPontryaginDual (p : ℕ) [Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Module ℤ_[p] A] :=
  A →ₗ[ℤ_[p]] PadicQuotientInt p

/-- The canonical quotient map from `ℚ_p` to `ℚ_p / ℤ_p`. -/
noncomputable def padicQuotientMap (p : ℕ) [Fact p.Prime] :
    ℚ_[p] →ₗ[ℤ_[p]] PadicQuotientInt p :=
  (LinearMap.range (Algebra.linearMap ℤ_[p] ℚ_[p])).mkQ

/-- The contragredient action of `g` on a p-adic Pontryagin-dual element. -/
noncomputable def contragredientSMul (p : ℕ) [Fact p.Prime] (G A : Type*) [Group G]
    [AddCommGroup A] [Module ℤ_[p] A] [DistribMulAction G A] [SMulCommClass G ℤ_[p] A]
    (g : G) (φ : PadicPontryaginDual p A) : PadicPontryaginDual p A where
  toFun a := φ (g⁻¹ • a)
  map_add' a b := by
    simp [smul_add, map_add]
  map_smul' r a := by
    change φ (g⁻¹ • (r • a)) = (RingHom.id ℤ_[p] r) • φ (g⁻¹ • a)
    rw [smul_comm g⁻¹ r a]
    simpa only [RingHom.id_apply] using φ.map_smul r (g⁻¹ • a)

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
