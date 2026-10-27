import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing Polynomial


/--
[IsLocalRing_exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  {P : Polynomial A}
  {r : ResidueField A}
-- given
  (hP : P.Monic)
  (hr : (P.map (residue A)).eval r = 0)
  (hr' : (P.map (residue A)).derivative.eval r ≠ 0) :
-- imply
  ∃ (t : AdicCompletion (IsLocalRing.maximalIdeal A) A) (a : A), aeval t P = 0 ∧ residue A a = r ∧
      t - algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a ∈
        (IsLocalRing.maximalIdeal A).map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
-- proof
  classical
    have : IsNoetherianRing A := inferInstance
    have h𝔪fg : (maximalIdeal A).FG := IsNoetherian.noetherian _
    let ι : A →+* AdicCompletion (maximalIdeal A) A := algebraMap A (AdicCompletion (maximalIdeal A) A)
    let I : Ideal (AdicCompletion (maximalIdeal A) A) := (maximalIdeal A).map ι
    have hI : IsAdicComplete I (AdicCompletion (maximalIdeal A) A) :=
      (IsAdicComplete.map_algebraMap_iff (maximalIdeal A) (AdicCompletion (maximalIdeal A) A)).mpr
        (AdicCompletion.isAdicComplete h𝔪fg)
    obtain ⟨a₀, ha₀⟩ := residue_surjective r
    have hres_eval : ∀ Q : Polynomial A, residue A (Q.eval a₀) = (Q.map (residue A)).eval r := by
      intro Q; rw [eval_map, ← ha₀, eval₂_at_apply]
    have h1 : P.eval a₀ ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff, hres_eval, hr]
    have h2 : IsUnit (P.derivative.eval a₀) := by
      by_contra h
      apply hr'
      rw [derivative_map, ← hres_eval, residue_eq_zero_iff]
      exact (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
    have hmonic : (P.map ι).Monic := hP.map ι
    have heval : (P.map ι).eval (ι a₀) ∈ I := by
      rw [eval_map, eval₂_at_apply]; exact Ideal.mem_map_of_mem ι h1
    have hunit : IsUnit (Ideal.Quotient.mk I ((P.map ι).derivative.eval (ι a₀))) := by
      rw [derivative_map, eval_map, eval₂_at_apply]
      exact (h2.map ι).map _
    obtain ⟨t, ht, hta⟩ := HenselianRing.is_henselian (I := I) (P.map ι) hmonic (ι a₀) heval hunit
    refine ⟨t, a₀, ?_, ha₀, hta⟩
    rwa [aeval_def, ← eval_map]


-- created on 2026-10-23
