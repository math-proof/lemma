/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean -/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Abbrev.NumberTheory.Padics.PontryaginDual
/-!
# Algebraic p-adic Pontryagin duals

This file defines the `ℤ_p`-linear dual `Hom(·, ℚ_p / ℤ_p)` and its
contragredient group action. No topology or continuity condition is imposed.
-/


namespace MetaMathlibExt

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

end MetaMathlibExt
