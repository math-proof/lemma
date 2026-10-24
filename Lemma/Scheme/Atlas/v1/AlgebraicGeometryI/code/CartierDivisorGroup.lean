import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorGroup
open CartierDivisorGroup
open scoped nonZeroDivisors
open FractionalIdeal


namespace CartierDivisorGroup

/--
[isPrincipal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorGroup.lean)
-/
@[path]
lemma isPrincipal_iff
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {D : CartierDivisorGroup A K} :
-- imply
  D ∈ (principalDivisor A K).range ↔ ∃ x : K, FractionalIdeal.spanSingleton A⁰ x = D.toFractionalIdeal A K := by
-- proof
  unfold principalDivisor toFractionalIdeal toUnits
  exact mem_principal_ideals_iff

end CartierDivisorGroup

namespace CartierDivisorGroup

/--
[linearlyEquivalent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorGroup.lean)
-/
@[path]
lemma linearlyEquivalent_iff
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {D₁ D₂ : CartierDivisorGroup A K} :
-- imply
  (QuotientGroup.mk' (principalDivisor A K).range D₁ = QuotientGroup.mk' (principalDivisor A K).range D₂) ↔ ∃ x : Kˣ, D₁ * principalDivisor A K x = D₂ := by
-- proof
  rw [QuotientGroup.mk'_eq_mk']
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, h⟩
    exact ⟨x, h⟩
  · rintro ⟨x, h⟩
    exact ⟨principalDivisor A K x, ⟨x, rfl⟩, h⟩

end CartierDivisorGroup


-- created on 2026-10-23
