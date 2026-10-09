import Mathlib
import sympy.Basic

open IsLocalRing Polynomial

/--
[ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat.lean)
-/
@[path]
private lemma main
  {A : ValuationSubring (AlgebraicClosure ℚ)} :
-- imply
  IsAlgClosed (ResidueField A) := by
-- proof
  refine IsAlgClosed.of_exists_root _ fun f hfm hfi => ?_

  have hsurj : Function.Surjective (residue A) := Ideal.Quotient.mk_surjective
  obtain ⟨F0, hF0⟩ := Polynomial.map_surjective _ hsurj f
  obtain ⟨F, hFmap, -, hFm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts f).mpr ⟨F0, hF0⟩) hfm

  let G := F.map (algebraMap A (AlgebraicClosure ℚ))
  have hGdeg : G.degree ≠ 0 := by
    have : G.degree = f.degree := by
      rw [show G = F.map _ from rfl, hFm.degree_map, ← hFmap, hFm.degree_map]
    rw [this]; exact (Polynomial.degree_pos_of_irreducible hfi).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root G hGdeg

  have hint : IsIntegral A α := ⟨F, hFm, by rwa [← Polynomial.eval_map]⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint

  refine ⟨residue A a, ?_⟩
  have hFa : F.eval a = 0 := by
    apply IsFractionRing.injective A (AlgebraicClosure ℚ)
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ha]; exact hα
  rw [← hFmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hFa, map_zero]


-- created on 2026-10-05
