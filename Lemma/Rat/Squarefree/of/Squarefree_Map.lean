import Mathlib
import sympy.Basic

open Polynomial

/--
[Polynomial_squarefree_of_squarefree_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_squarefree_of_squarefree_map.lean)
-/
@[main]
private lemma main
  {κ L : Type*} [Field κ] [CommRing L] [IsDomain L]
  {φ : κ →+* L}
  {f : κ[X]}
-- given
  (hf : Squarefree (f.map φ)) :
-- imply
  Squarefree f := by
-- proof
  have hφ : Function.Injective φ := φ.injective
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  intro g hg
  have hgmap : IsUnit (g.map φ) := by
    apply hf
    have := _root_.map_dvd (Polynomial.mapRingHom φ) hg
    simpa [Polynomial.map_mul] using this
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hg
    exact hf0 hg
  rw [Polynomial.isUnit_iff] at hgmap ⊢
  obtain ⟨r, hr, hrg⟩ := hgmap
  have hdeg : g.natDegree = 0 := by
    rw [← natDegree_map_eq_of_injective hφ, ← hrg, natDegree_C]
  refine ⟨g.coeff 0, ?_, (eq_C_of_natDegree_eq_zero hdeg).symm⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hg0
  rw [eq_C_of_natDegree_eq_zero hdeg, h0, map_zero]


-- created on 2026-10-05
