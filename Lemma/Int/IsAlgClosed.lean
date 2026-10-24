import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma isAlgClosed_of_surjective
  {R L F : Type*} [CommRing R] [Field L] [IsAlgClosed L]
  [Algebra R L] [Field F] (φ : integralClosure R L →+* F) (hφ : Function.Surjective φ) :
  IsAlgClosed F := by
  refine IsAlgClosed.of_exists_root F fun f hf hirr => ?_
  obtain ⟨g, hgf, hdeg, hgmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (Polynomial.mem_lifts_of_surjective hφ f) hf
  have hdegL : (g.map (algebraMap (integralClosure R L) L)).degree ≠ 0 := by
    rw [hgmon.degree_map, hdeg]
    refine fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr h |>.elim
      (fun u hu => ⟨u, hu⟩))
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdegL
  have hαint : IsIntegral (integralClosure R L) α := ⟨g, hgmon, by
    rw [Polynomial.eval₂_eq_eval_map]
    refine hα⟩
  have hαR : IsIntegral R α := isIntegral_trans (R := R) α hαint
  let a : integralClosure R L := ⟨α, hαR⟩
  have hga : g.eval a = 0 := by
    have h1 : algebraMap (integralClosure R L) L (g.eval a) = 0 := by
      have h2 : (g.map (algebraMap (integralClosure R L) L)).eval
        (algebraMap (integralClosure R L) L a) = 0 := hα
      rwa [Polynomial.eval_map, Polynomial.eval₂_at_apply] at h2
    refine (FaithfulSMul.algebraMap_injective (integralClosure R L) L)
      (by rw [h1, map_zero])
  refine ⟨φ a, ?_⟩
  rw [← hgf, Polynomial.eval_map, Polynomial.eval₂_at_apply, hga, map_zero]
/--
[integralClosure_isAlgClosed_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_integralClosure_isAlgClosed_of_surjective.lean)
-/
@[path]
private lemma main
  [CommRing R] [Field L] [IsAlgClosed L] [Algebra R L] [Field F]
  (φ : integralClosure R L →+* F) (hφ : Function.Surjective φ) :
  -- imply
  IsAlgClosed F :=
  isAlgClosed_of_surjective φ hφ


-- created on 2026-10-20
