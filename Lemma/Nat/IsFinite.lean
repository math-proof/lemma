import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_IsFinite_of_isFinite_comp_of_surjective_of_isProper](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsFinite_of_isFinite_comp_of_surjective_of_isProper.lean)
-/
@[main]
private lemma main
  {X₀ X Y : Scheme.{u}}
  {i : X₀ ⟶ X} [Surjective i]
  {g : X ⟶ Y} [IsProper g] [IsFinite (i ≫ g)] :
-- imply
  IsFinite g := by
-- proof
  have hq : LocallyQuasiFinite g := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton g fun y => ?_
    have hfin : ((i ≫ g) ⁻¹' {y}).Finite := (i ≫ g).finite_preimage_singleton y
    refine (hfin.image i).subset ?_
    intro x hx
    obtain ⟨x₀, rfl⟩ := ‹Surjective i›.surj x
    exact ⟨x₀, by simpa [Scheme.Hom.comp_base] using hx, rfl⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite g


-- created on 2026-10-05
