import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry TopologicalSpace

/--
[AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton.lean)
-/
@[main]
private lemma main
  {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
-- given
  (hdim : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X)) :
-- imply
  ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite := by
-- proof
  intro Z hZ hne
  obtain ⟨S, hSfin, hSclosed, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine Set.Finite.sUnion hSfin fun t ht => ?_

  obtain ⟨z, hz⟩ := QuasiSober.sober (hSirr t ht) (hSclosed t ht)
  have hzne : z ≠ genericPoint X := by
    rintro rfl
    apply hne
    apply Set.eq_univ_of_univ_subset
    calc Set.univ = closure ({genericPoint X} : Set X) := (genericPoint_closure X).symm
      _ = t := hz.def
      _ ⊆ ⋃₀ S := Set.subset_sUnion_of_mem ht
  have ht1 : t = {z} := by rw [← hz.def, (hdim z hzne).closure_eq]
  rw [ht1]
  exact Set.finite_singleton z


-- created on 2026-10-05
