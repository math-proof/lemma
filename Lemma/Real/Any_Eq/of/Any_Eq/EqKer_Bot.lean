import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot.lean)
-/
@[path]
private lemma main
  {T T' A Z : Scheme.{0}}
  {π : T' ⟶ T}
  {y : T ⟶ A}
  {ι : Z ⟶ A} [IsClosedImmersion ι]
-- given
  (hπ : π.ker = ⊥)
  (h : ∃ z' : T' ⟶ Z, z' ≫ ι = π ≫ y) :
-- imply
  ∃ z : T ⟶ Z, z ≫ ι = y := by
-- proof
  obtain ⟨z', hz'⟩ := h
  have hle : ι.ker ≤ y.ker := by
    calc ι.ker ≤ (z' ≫ ι).ker := Scheme.Hom.le_ker_comp z' ι
      _ = (π ≫ y).ker := by rw [hz']
      _ = (π.ker).map y := Scheme.Hom.ker_comp π y
      _ = y.ker := by rw [hπ, Scheme.IdealSheafData.map_bot]
  exact ⟨IsClosedImmersion.lift ι y hle, IsClosedImmersion.lift_fac ι y hle⟩


-- created on 2026-10-05
