import Mathlib
import sympy.Basic


/--
[ValuationSubring_algHom_apply_mem_of_moduleFinite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_algHom_apply_mem_of_moduleFinite.lean)
-/
@[main]
private lemma main
  [CommRing R] [Field L] [Algebra R L] [CommRing H] [Algebra R H] [Module.Finite R H]
  {A : ValuationSubring L}
  {f : H →ₐ[R] L}
-- given
  (hR : ∀ r : R, algebraMap R L r ∈ A)
  (h : H) :
-- imply
  f h ∈ A := by
-- proof
  letI : Algebra R A := ((algebraMap R L).codRestrict A.toSubring hR).toAlgebra
  haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hint : IsIntegral R (f h) := (Algebra.IsIntegral.isIntegral (R := R) h).map f
  have hintA : IsIntegral A (f h) := hint.tower_top

  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintA
  rw [← ha]
  exact a.2


-- created on 2026-10-05
