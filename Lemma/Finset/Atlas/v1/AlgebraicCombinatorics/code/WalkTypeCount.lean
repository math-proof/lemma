import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkTypeCount
open HasseWalks WalkTypeCount in
open scoped Nat


namespace WalkTypeCount

/--
[applyStepWord_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma applyStepWord_add
  {w : List HStep}
  {f g : YoungDiagram →₀ ℤ} :
-- imply
  applyStepWord w (f + g) = applyStepWord w f + applyStepWord w g := by
-- proof
  induction w generalizing f g with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | U =>
      show applyStepWord rest (WalkCountFormula.liftU (f + g)) =
        applyStepWord rest (WalkCountFormula.liftU f) +
        applyStepWord rest (WalkCountFormula.liftU g)
      rw [map_add]; exact ih _ _
    | D =>
      show applyStepWord rest (WalkCountFormula.liftD (f + g)) =
        applyStepWord rest (WalkCountFormula.liftD f) +
        applyStepWord rest (WalkCountFormula.liftD g)
      rw [map_add]; exact ih _ _

end WalkTypeCount

namespace WalkTypeCount

/--
[applyStepWord_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma applyStepWord_smul
  {w : List HStep}
  {c : ℤ}
  {f : YoungDiagram →₀ ℤ} :
-- imply
  applyStepWord w (c • f) = c • applyStepWord w f := by
-- proof
  induction w generalizing f with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | U =>
      show applyStepWord rest (WalkCountFormula.liftU (c • f)) =
        c • applyStepWord rest (WalkCountFormula.liftU f)
      rw [map_smul]; exact ih _
    | D =>
      show applyStepWord rest (WalkCountFormula.liftD (c • f)) =
        c • applyStepWord rest (WalkCountFormula.liftD f)
      rw [map_smul]; exact ih _

end WalkTypeCount

namespace WalkTypeCount

/--
[applyStepWord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma applyStepWord_zero
  {w : List HStep} :
-- imply
  applyStepWord w 0 = 0 := by
-- proof
  induction w with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | U =>
      show applyStepWord rest (WalkCountFormula.liftU 0) = 0
      rw [map_zero]; exact ih
    | D =>
      show applyStepWord rest (WalkCountFormula.liftD 0) = 0
      rw [map_zero]; exact ih

end WalkTypeCount

namespace WalkTypeCount

/--
[applyStepWord_smul_iterU_emptyBasis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma applyStepWord_smul_iterU_emptyBasis
  {w : List HStep}
  {c : ℤ}
  {m : ℕ} :
-- imply
  applyStepWord w (c • WalkCountFormula.iterU m WalkCountFormula.emptyBasis) = (c * downFactor w m) • WalkCountFormula.iterU (finalLevel w m) WalkCountFormula.emptyBasis := by
-- proof
  induction w generalizing c m with
  | nil =>
    simp only [applyStepWord, downFactor, finalLevel, mul_one]
  | cons s rest ih =>
    cases s with
    | U =>
      show applyStepWord rest (WalkCountFormula.liftU (c • WalkCountFormula.iterU m WalkCountFormula.emptyBasis)) = _
      rw [map_smul, ← LinearMap.comp_apply, ← WalkCountFormula.iterU_succ']
      exact ih c (m + 1)
    | D =>
      show applyStepWord rest (WalkCountFormula.liftD (c • WalkCountFormula.iterU m WalkCountFormula.emptyBasis)) = _
      rw [map_smul, WalkCountFormula.liftD_iterU_emptyBasis, ← mul_smul]
      rw [ih (c * (m : ℤ)) (m - 1)]
      simp only [downFactor, finalLevel]; ring_nf

end WalkTypeCount

namespace WalkTypeCount

/--
[applyStepWord_emptyBasis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma applyStepWord_emptyBasis_eq
  {w : List HStep} :
-- imply
  applyStepWord w WalkCountFormula.emptyBasis = downFactor w 0 • WalkCountFormula.iterU (finalLevel w 0) WalkCountFormula.emptyBasis := by
-- proof
  have h := applyStepWord_smul_iterU_emptyBasis w 1 0
  simp only [WalkCountFormula.iterU_zero, LinearMap.id_apply, one_smul, one_mul] at h
  exact h

end WalkTypeCount

namespace WalkTypeCount

/--
[runningLevel_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma runningLevel_zero
  {w : List HStep} :
-- imply
  runningLevel w 0 = 0 := by
-- proof
  simp [runningLevel]

end WalkTypeCount

namespace WalkTypeCount

/--
[runningLevel_cons_U_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma runningLevel_cons_U_succ
  {rest : List HStep}
  {k : ℕ} :
-- imply
  runningLevel (HStep.U :: rest) (k + 1) = 1 + runningLevel rest k := by
-- proof
  simp only [runningLevel, List.take_succ_cons, List.filter_cons, beq_iff_eq]
  simp (config := { decide := true }) only [ite_true, ite_false, List.length_cons]
  push_cast; ring

end WalkTypeCount

namespace WalkTypeCount

/--
[runningLevel_cons_D_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma runningLevel_cons_D_succ
  {rest : List HStep}
  {k : ℕ} :
-- imply
  runningLevel (HStep.D :: rest) (k + 1) = runningLevel rest k - 1 := by
-- proof
  simp only [runningLevel, List.take_succ_cons, List.filter_cons, beq_iff_eq]
  simp (config := { decide := true }) only [ite_true, ite_false, List.length_cons]
  push_cast; ring
set_option maxHeartbeats 400000 in

end WalkTypeCount

namespace WalkTypeCount

/--
[finalLevel_eq_of_valid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma finalLevel_eq_of_valid
  {w : List HStep}
  {m : ℕ}
-- given
  (hvalid : ∀ k : ℕ, k ≤ w.length → 0 ≤ (m : ℤ) + runningLevel w k) :
-- imply
  (finalLevel w m : ℤ) = (m : ℤ) + runningLevel w w.length := by
-- proof
  induction w generalizing m with
  | nil => simp [finalLevel, runningLevel]
  | cons s rest ih =>
    cases s with
    | U =>
      simp only [finalLevel, List.length_cons]
      have hvalid' : ∀ k : ℕ, k ≤ rest.length →
        0 ≤ ((m + 1 : ℕ) : ℤ) + runningLevel rest k := by
        intro k hk
        have := hvalid (k + 1) (by simp [List.length_cons]; omega)
        rw [runningLevel_cons_U_succ] at this
        push_cast at this ⊢; linarith
      rw [ih (m + 1) hvalid', runningLevel_cons_U_succ]
      push_cast; ring
    | D =>
      simp only [finalLevel, List.length_cons]
      have hm_pos : 1 ≤ (m : ℤ) := by
        have := hvalid 1 (by simp [List.length_cons])
        rw [runningLevel_cons_D_succ] at this
        simp only [runningLevel_zero] at this; linarith
      have hvalid' : ∀ k : ℕ, k ≤ rest.length →
        0 ≤ ((m - 1 : ℕ) : ℤ) + runningLevel rest k := by
        intro k hk
        have := hvalid (k + 1) (by simp only [List.length_cons]; omega)
        rw [runningLevel_cons_D_succ] at this
        omega
      rw [ih (m - 1) hvalid', runningLevel_cons_D_succ]
      omega

end WalkTypeCount

namespace WalkTypeCount

/--
[numURight_sub_numDRight_eq_runningLevel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma numURight_sub_numDRight_eq_runningLevel
  {w : List HStep}
  {i : Fin w.length} :
-- imply
  (numURight w i : ℤ) - (numDRight w i : ℤ) = runningLevel w i.val := by
-- proof
  simp only [numURight, numDRight, runningLevel]

end WalkTypeCount

namespace WalkTypeCount

/--
[downStepProduct_eq_prod_runningLevel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma downStepProduct_eq_prod_runningLevel
  {w : List HStep} :
-- imply
  downStepProduct w = ∏ i ∈ downPositions w, runningLevel w i.val := by
-- proof
  simp only [downStepProduct, numURight_sub_numDRight_eq_runningLevel]
set_option maxHeartbeats 400000 in

end WalkTypeCount

namespace WalkTypeCount

/--
[downFactor_eq_downStepProduct_offset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma downFactor_eq_downStepProduct_offset
  {w : List HStep}
  {m : ℕ}
-- given
  (hvalid : ∀ k : ℕ, k ≤ w.length → 0 ≤ (m : ℤ) + runningLevel w k) :
-- imply
  downFactor w m = ∏ i ∈ downPositions w, ((m : ℤ) + runningLevel w i.val) := by
-- proof
  induction w generalizing m with
  | nil =>
    simp [downFactor, downPositions]
  | cons s rest ih =>
    cases s with
    | U =>
      simp only [downFactor]
      have hvalid' : ∀ k, k ≤ rest.length →
        0 ≤ ((m + 1 : ℕ) : ℤ) + runningLevel rest k := by
        intro k hk
        have := hvalid (k + 1) (by simp [List.length_cons]; omega)
        rw [runningLevel_cons_U_succ] at this; push_cast at this ⊢; linarith
      rw [ih (m + 1) hvalid']
      apply Finset.prod_nbij (fun (i : Fin rest.length) => (⟨i.val + 1, by simp [List.length_cons]⟩ : Fin (HStep.U :: rest).length))
      · intro ⟨i, hi_lt⟩ hi_mem
        simp only [downPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hi_mem ⊢
        show (HStep.U :: rest)[i + 1]'(by simp [List.length_cons]; omega) = HStep.D
        simp only [List.getElem_cons_succ]
        exact hi_mem
      · intro i _ j _ h; simp [Fin.ext_iff] at h; exact Fin.ext (by omega)
      · intro ⟨j, hj⟩ hj_mem
        simp only [downPositions, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_image,
          Finset.mem_coe] at hj_mem ⊢
        cases j with
        | zero =>
          exfalso
          have : HStep.U = HStep.D := by simp at hj_mem
          exact HStep.noConfusion this
        | succ j' =>
          have hj' : j' < rest.length := by simp [List.length_cons] at hj; omega
          refine ⟨⟨j', hj'⟩, ?_, by simp⟩
          have hd : (HStep.U :: rest)[j' + 1] = HStep.D := by simp at hj_mem; exact hj_mem
          simpa [downPositions, Finset.mem_filter, List.getElem_cons_succ] using hd
      · intro ⟨i, hi_lt⟩ _
        simp only [runningLevel_cons_U_succ]; push_cast; ring
    | D =>
      simp only [downFactor]
      have hm_pos : 1 ≤ (m : ℤ) := by
        have := hvalid 1 (by simp [List.length_cons])
        rw [runningLevel_cons_D_succ] at this
        simp only [runningLevel_zero] at this; linarith
      have hvalid' : ∀ k, k ≤ rest.length →
        0 ≤ ((m - 1 : ℕ) : ℤ) + runningLevel rest k := by
        intro k hk
        have := hvalid (k + 1) (by simp only [List.length_cons]; omega)
        rw [runningLevel_cons_D_succ] at this; omega
      rw [ih (m - 1) hvalid']
      have h0_mem : (⟨0, by simp⟩ : Fin (HStep.D :: rest).length) ∈ downPositions (HStep.D :: rest) := by
        simp only [downPositions, Finset.mem_filter, Finset.mem_univ, true_and]
        show (HStep.D :: rest)[0] = HStep.D
        simp
      rw [← Finset.mul_prod_erase _ _ h0_mem]
      have : (↑m + runningLevel (HStep.D :: rest) 0) = (m : ℤ) := by simp [runningLevel]
      rw [this]
      congr 1
      apply Finset.prod_nbij (fun (i : Fin rest.length) => (⟨i.val + 1, by simp [List.length_cons]⟩ : Fin (HStep.D :: rest).length))
      · intro ⟨i, hi_lt⟩ hi_mem
        simp only [downPositions, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, ne_eq, Fin.ext_iff] at hi_mem ⊢
        constructor
        · omega
        · show (HStep.D :: rest)[i + 1]'(by simp [List.length_cons]; exact hi_lt) = HStep.D
          simp only [List.getElem_cons_succ]; exact hi_mem
      · intro i _ j _ h; simp [Fin.ext_iff] at h; exact Fin.ext (by omega)
      · intro ⟨j, hj⟩ hj_mem
        simp only [downPositions, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
          true_and, Set.mem_image, Finset.mem_coe, Fin.ext_iff, ne_eq] at hj_mem ⊢
        obtain ⟨hne, hd⟩ := hj_mem
        cases j with
        | zero => exact absurd rfl hne
        | succ j' =>
          have hj' : j' < rest.length := by simp [List.length_cons] at hj; omega
          refine ⟨⟨j', hj'⟩, ?_, by simp⟩
          have hd' : (HStep.D :: rest)[j' + 1] = HStep.D := by simp at hd; exact hd
          simpa [downPositions, Finset.mem_filter, List.getElem_cons_succ] using hd'
      · intro ⟨i, hi_lt⟩ _
        simp only [runningLevel_cons_D_succ]; omega

end WalkTypeCount

namespace WalkTypeCount

/--
[downFactor_zero_eq_downStepProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma downFactor_zero_eq_downStepProduct
  {w : List HStep}
-- given
  (hvalid : ∀ k : ℕ, k ≤ w.length → 0 ≤ runningLevel w k) :
-- imply
  downFactor w 0 = downStepProduct w := by
-- proof
  rw [downFactor_eq_downStepProduct_offset w 0 (by simpa using hvalid)]
  rw [downStepProduct_eq_prod_runningLevel]
  simp only [Nat.cast_zero, zero_add]
end WalkTypeCount


/--
[WalkTypeCount.natCard_hasseWalk_cons_U_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma WalkTypeCount.natCard_hasseWalk_cons_U_eq_sum
  {rest : List HasseWalks.HStep}
  {start lam : YoungDiagram} :
-- imply
  (Nat.card (HasseWalks.HasseWalk (HasseWalks.HStep.U :: rest) start lam) : ℤ) = ∑ μ ∈ start.coversUp, (Nat.card (HasseWalks.HasseWalk rest μ lam) : ℤ) := by
-- proof
  classical
  have hlen : (HasseWalks.HStep.U :: rest).length = rest.length + 1 := rfl
  norm_cast
  let S := start.coversUp
  let fwd : HasseWalks.HasseWalk (HasseWalks.HStep.U :: rest) start lam →
    (μ : ↑S) × HasseWalks.HasseWalk rest μ lam := fun w =>
    let μ := w.diagram ⟨1, by omega⟩
    have hcov_raw : start ⋖ μ := by
      have := w.step_up ⟨0, by omega⟩ (by simp)
      simp only [μ]; convert this using 2 <;> exact w.start_eq.symm
    have hμ_mem : μ ∈ S := YoungDiagram.mem_coversUp_of_covBy hcov_raw
    let g : Fin (rest.length + 1) → YoungDiagram := fun i => w.diagram ⟨i.val + 1, by omega⟩
    ⟨⟨μ, hμ_mem⟩, ⟨g, rfl,
      by show w.diagram ⟨rest.length + 1, _⟩ = lam; convert w.target_eq using 2,
      fun ⟨i, hi⟩ hstep => by
        show w.diagram ⟨i + 1, _⟩ ⋖ w.diagram ⟨i + 2, _⟩
        have h1 : (HasseWalks.HStep.U :: rest)[i + 1]'(by rw [hlen]; omega) = HasseWalks.HStep.U := by
          simp [List.getElem_cons_succ]; exact hstep
        convert w.step_up ⟨i + 1, by rw [hlen]; omega⟩ h1 using 2,
      fun ⟨i, hi⟩ hstep => by
        show w.diagram ⟨i + 2, _⟩ ⋖ w.diagram ⟨i + 1, _⟩
        have h1 : (HasseWalks.HStep.U :: rest)[i + 1]'(by rw [hlen]; omega) = HasseWalks.HStep.D := by
          simp [List.getElem_cons_succ]; exact hstep
        convert w.step_down ⟨i + 1, by rw [hlen]; omega⟩ h1 using 2⟩⟩
  let bwd : ((μ : ↑S) × HasseWalks.HasseWalk rest μ lam) →
    HasseWalks.HasseWalk (HasseWalks.HStep.U :: rest) start lam := fun ⟨⟨μ, hμ⟩, gw⟩ =>
    have hcov : start ⋖ μ := YoungDiagram.covBy_of_mem_coversUp hμ
    let w : Fin (rest.length + 2) → YoungDiagram := fun i =>
      if h : 1 ≤ i.val then gw.diagram ⟨i.val - 1, by omega⟩ else start
    ⟨w,
      by simp only [w, show ¬(1 ≤ 0) from by omega, dite_false],
      by simp only [w, show 1 ≤ rest.length + 1 from by omega, dite_true]; show gw.diagram ⟨rest.length + 1 - 1, _⟩ = lam; convert gw.target_eq using 2,
      fun ⟨i, hi⟩ hstep => by
        simp only [w]; rcases i with _ | i
        · simp only [show ¬(1 ≤ 0) from by omega, dite_false, show 1 ≤ 0 + 1 from by omega, dite_true]
          have h1 : gw.diagram ⟨0 + 1 - 1, by omega⟩ = μ := by convert gw.start_eq using 2
          have h2 : μ = gw.diagram ⟨0, by omega⟩ := gw.start_eq.symm
          rw [h1]; exact hcov
        · simp only [show 1 ≤ i + 1 from by omega, dite_true, show 1 ≤ i + 1 + 1 from by omega, dite_true]
          have : rest[i]'(by rw [hlen] at hi; omega) = HasseWalks.HStep.U := by
            simpa [List.getElem_cons_succ] using hstep
          convert gw.step_up ⟨i, by rw [hlen] at hi; omega⟩ this using 2 <;> congr 1 <;> omega,
      fun ⟨i, hi⟩ hstep => by
        simp only [w]; rcases i with _ | i
        · simp at hstep
        · simp only [show 1 ≤ i + 1 + 1 from by omega, dite_true, show 1 ≤ i + 1 from by omega, dite_true]
          have : rest[i]'(by rw [hlen] at hi; omega) = HasseWalks.HStep.D := by
            simpa [List.getElem_cons_succ] using hstep
          convert gw.step_down ⟨i, by rw [hlen] at hi; omega⟩ this using 2⟩
  have hfwd_bwd : Function.RightInverse bwd fwd := by
    intro ⟨⟨μ, hμ⟩, gw⟩
    show fwd (bwd ⟨⟨μ, hμ⟩, gw⟩) = ⟨⟨μ, hμ⟩, gw⟩
    simp only [fwd, bwd]
    have h_μ_eq : (if h : 1 ≤ 1 then gw.diagram ⟨1 - 1, by omega⟩ else start) = μ := by
      rw [dif_pos le_rfl]; convert gw.start_eq using 2
    have h_diag_eq : (fun (i : Fin (rest.length + 1)) =>
      if h : 1 ≤ i.val + 1 then gw.diagram ⟨i.val + 1 - 1, by omega⟩ else start) = gw.diagram :=
      funext fun ⟨j, hj⟩ => by rw [dif_pos (by omega)]; congr
    simp only [h_μ_eq, h_diag_eq, Sigma.mk.inj_iff, true_and]
    congr 1; exact proof_irrel_heq _ _
  have hbwd_fwd : ∀ x, bwd (fwd x) = x := by
    intro ⟨d, se, te, su, sd⟩; simp only [fwd, bwd]; congr 1; funext ⟨j, hj⟩
    show (if h : 1 ≤ j then d ⟨j - 1 + 1, _⟩ else start) = d ⟨j, hj⟩
    split_ifs with h
    · show d ⟨j - 1 + 1, _⟩ = d ⟨j, hj⟩; congr 1; simp [Fin.ext_iff]; omega
    · simp only [show j = 0 from by omega] at se ⊢; exact se.symm
  have equiv : HasseWalks.HasseWalk (HasseWalks.HStep.U :: rest) start lam ≃
    ((μ : ↑S) × HasseWalks.HasseWalk rest μ lam) :=
    { toFun := fwd, invFun := bwd, left_inv := hbwd_fwd, right_inv := hfwd_bwd }
  rw [Nat.card_congr equiv, Nat.card_sigma,
    Finset.sum_coe_sort S (fun μ => Nat.card (HasseWalks.HasseWalk rest μ lam))]
set_option maxHeartbeats 800000 in

/--
[WalkTypeCount.natCard_hasseWalk_cons_D_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma WalkTypeCount.natCard_hasseWalk_cons_D_eq_sum
  {rest : List HasseWalks.HStep}
  {start lam : YoungDiagram} :
-- imply
  (Nat.card (HasseWalks.HasseWalk (HasseWalks.HStep.D :: rest) start lam) : ℤ) = ∑ μ ∈ start.coversDown, (Nat.card (HasseWalks.HasseWalk rest μ lam) : ℤ) := by
-- proof
  classical
  have hlen : (HasseWalks.HStep.D :: rest).length = rest.length + 1 := rfl
  norm_cast
  let S := start.coversDown
  let fwd : HasseWalks.HasseWalk (HasseWalks.HStep.D :: rest) start lam →
    (μ : ↑S) × HasseWalks.HasseWalk rest μ lam := fun w =>
    let μ := w.diagram ⟨1, by omega⟩
    have hcov_raw : μ ⋖ start := by
      have := w.step_down ⟨0, by omega⟩ (by simp)
      simp only [μ]; convert this using 2; exact w.start_eq.symm
    have hμ_mem : μ ∈ S := YoungDiagram.mem_coversDown_of_covBy hcov_raw
    let g : Fin (rest.length + 1) → YoungDiagram := fun i => w.diagram ⟨i.val + 1, by omega⟩
    ⟨⟨μ, hμ_mem⟩, ⟨g, rfl,
      by show w.diagram ⟨rest.length + 1, _⟩ = lam; convert w.target_eq using 2,
      fun ⟨i, hi⟩ hstep => by
        show w.diagram ⟨i + 1, _⟩ ⋖ w.diagram ⟨i + 2, _⟩
        have h1 : (HasseWalks.HStep.D :: rest)[i + 1]'(by rw [hlen]; omega) = HasseWalks.HStep.U := by
          simp [List.getElem_cons_succ]; exact hstep
        convert w.step_up ⟨i + 1, by rw [hlen]; omega⟩ h1 using 2,
      fun ⟨i, hi⟩ hstep => by
        show w.diagram ⟨i + 2, _⟩ ⋖ w.diagram ⟨i + 1, _⟩
        have h1 : (HasseWalks.HStep.D :: rest)[i + 1]'(by rw [hlen]; omega) = HasseWalks.HStep.D := by
          simp [List.getElem_cons_succ]; exact hstep
        convert w.step_down ⟨i + 1, by rw [hlen]; omega⟩ h1 using 2⟩⟩
  let bwd : ((μ : ↑S) × HasseWalks.HasseWalk rest μ lam) →
    HasseWalks.HasseWalk (HasseWalks.HStep.D :: rest) start lam := fun ⟨⟨μ, hμ⟩, gw⟩ =>
    have hcov : μ ⋖ start := YoungDiagram.covBy_of_mem_coversDown hμ
    let w : Fin (rest.length + 2) → YoungDiagram := fun i =>
      if h : 1 ≤ i.val then gw.diagram ⟨i.val - 1, by omega⟩ else start
    ⟨w,
      by simp only [w, show ¬(1 ≤ 0) from by omega, dite_false],
      by simp only [w]; show gw.diagram ⟨rest.length + 1 - 1, _⟩ = lam; convert gw.target_eq using 2,
      fun ⟨i, hi⟩ hstep => by
        simp only [w]; rcases i with _ | i
        · simp at hstep
        · simp only [show 1 ≤ i + 1 from by omega, dite_true, show 1 ≤ i + 1 + 1 from by omega, dite_true]
          have : rest[i]'(by rw [hlen] at hi; omega) = HasseWalks.HStep.U := by
            simpa [List.getElem_cons_succ] using hstep
          convert gw.step_up ⟨i, by rw [hlen] at hi; omega⟩ this using 2,
      fun ⟨i, hi⟩ hstep => by
        simp only [w]; rcases i with _ | i
        · simp only [show ¬(1 ≤ 0) from by omega, dite_false, show 1 ≤ 0 + 1 from by omega, dite_true]
          have h1 : gw.diagram ⟨0 + 1 - 1, by omega⟩ = μ := by convert gw.start_eq using 2
          rw [h1]; exact hcov
        · simp only [show 1 ≤ i + 1 + 1 from by omega, dite_true, show 1 ≤ i + 1 from by omega, dite_true]
          have : rest[i]'(by rw [hlen] at hi; omega) = HasseWalks.HStep.D := by
            simpa [List.getElem_cons_succ] using hstep
          convert gw.step_down ⟨i, by rw [hlen] at hi; omega⟩ this using 2⟩
  have hfwd_bwd : Function.RightInverse bwd fwd := by
    intro ⟨⟨μ, hμ⟩, gw⟩
    show fwd (bwd ⟨⟨μ, hμ⟩, gw⟩) = ⟨⟨μ, hμ⟩, gw⟩
    simp only [fwd, bwd]
    have h_μ_eq : (if h : 1 ≤ 1 then gw.diagram ⟨1 - 1, by omega⟩ else start) = μ := by
      rw [dif_pos le_rfl]; convert gw.start_eq using 2
    have h_diag_eq : (fun (i : Fin (rest.length + 1)) =>
      if h : 1 ≤ i.val + 1 then gw.diagram ⟨i.val + 1 - 1, by omega⟩ else start) = gw.diagram :=
      funext fun ⟨j, hj⟩ => by rw [dif_pos (by omega)]; congr
    simp only [h_μ_eq, h_diag_eq, Sigma.mk.inj_iff, true_and]
    congr 1; exact proof_irrel_heq _ _
  have hbwd_fwd : ∀ x, bwd (fwd x) = x := by
    intro ⟨d, se, te, su, sd⟩; simp only [fwd, bwd]; congr 1; funext ⟨j, hj⟩
    show (if h : 1 ≤ j then d ⟨j - 1 + 1, _⟩ else start) = d ⟨j, hj⟩
    split_ifs with h
    · show d ⟨j - 1 + 1, _⟩ = d ⟨j, hj⟩; congr 1; simp [Fin.ext_iff]; omega
    · simp only [show j = 0 from by omega] at se ⊢; exact se.symm
  have equiv : HasseWalks.HasseWalk (HasseWalks.HStep.D :: rest) start lam ≃
    ((μ : ↑S) × HasseWalks.HasseWalk rest μ lam) :=
    { toFun := fwd, invFun := bwd, left_inv := hbwd_fwd, right_inv := hfwd_bwd }
  rw [Nat.card_congr equiv, Nat.card_sigma,
    Finset.sum_coe_sort S (fun μ => Nat.card (HasseWalks.HasseWalk rest μ lam))]
noncomputable section
open HasseWalks

namespace WalkTypeCount

/--
[applyStepWord_finset_sum_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma applyStepWord_finset_sum_single
  {w : List HStep}
  {S : Finset YoungDiagram} :
-- imply
  applyStepWord w (S.sum (fun σ => Finsupp.single σ 1)) = S.sum (fun σ => applyStepWord w (Finsupp.single σ 1)) := by
-- proof
  classical
  induction S using Finset.cons_induction_on with
  | empty => simp [applyStepWord_zero]
  | cons a S hnotin ih =>
    rw [Finset.sum_cons, applyStepWord_add, ih, Finset.sum_cons]

end WalkTypeCount

namespace WalkTypeCount

/--
[walkTypeCount_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma walkTypeCount_general
  {w : List HStep}
  {start lam : YoungDiagram} :
-- imply
  (Nat.card (HasseWalk w start lam) : ℤ) = (applyStepWord w (Finsupp.single start 1)) lam := by
-- proof
  classical
  induction w generalizing start with
  | nil =>
    simp only [applyStepWord]
    by_cases h : start = lam
    · subst h
      rw [Finsupp.single_eq_same]
      have : Nat.card (HasseWalk [] start start) = 1 := by
        apply Nat.card_eq_one_iff_unique.mpr
        refine ⟨⟨fun ⟨d1, s1, t1, _, _⟩ ⟨d2, s2, t2, _, _⟩ => ?_⟩,
          ⟨⟨fun _ => start, rfl, rfl,
            fun ⟨i, hi⟩ => absurd hi (by simp),
            fun ⟨i, hi⟩ => absurd hi (by simp)⟩⟩⟩
        congr 1; funext ⟨j, hj⟩
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0; exact s1.trans s2.symm
      simp [this]
    · simp only [Finsupp.single_apply, if_neg h]
      have hempty : IsEmpty (HasseWalk [] start lam) := by
        constructor; intro ⟨d, s_eq, t_eq, _, _⟩
        exact h (s_eq.symm.trans t_eq)
      haveI := hempty
      simp [Nat.card_of_isEmpty]
  | cons s rest ih =>
    cases s with
    | U =>
      show (Nat.card (HasseWalk (HStep.U :: rest) start lam) : ℤ) =
        (applyStepWord rest (WalkCountFormula.liftU (Finsupp.single start 1))) lam
      rw [WalkCountFormula.liftU_single_one]
      simp only [YoungDiagram.raisingOp]
      rw [applyStepWord_finset_sum_single, Finset.sum_apply']
      rw [natCard_hasseWalk_cons_U_eq_sum]
      congr 1; ext μ; exact ih μ
    | D =>
      show (Nat.card (HasseWalk (HStep.D :: rest) start lam) : ℤ) =
        (applyStepWord rest (WalkCountFormula.liftD (Finsupp.single start 1))) lam
      rw [WalkCountFormula.liftD_single_one]
      simp only [YoungDiagram.loweringOp]
      rw [applyStepWord_finset_sum_single, Finset.sum_apply']
      rw [natCard_hasseWalk_cons_D_eq_sum]
      congr 1; ext μ; exact ih μ
end WalkTypeCount
end


/--
[WalkTypeCount.walkTypeCount_eq_applyStepWord_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma WalkTypeCount.walkTypeCount_eq_applyStepWord_coeff
  {w : List HasseWalks.HStep}
  {lam : YoungDiagram} :
-- imply
  (WalkTypeCount.walkTypeCount w lam : ℤ) = (WalkTypeCount.applyStepWord w WalkCountFormula.emptyBasis) lam := by
-- proof
  show (Nat.card (HasseWalks.HasseWalk w ⊥ lam) : ℤ) =
    (WalkTypeCount.applyStepWord w WalkCountFormula.emptyBasis) lam
  rw [WalkCountFormula.emptyBasis]
  exact WalkTypeCount.walkTypeCount_general w ⊥ lam

/--
[WalkTypeCount.applyStepWord_emptyBasis_eq_downStepProduct_smul_iterU](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma WalkTypeCount.applyStepWord_emptyBasis_eq_downStepProduct_smul_iterU
  {w : List HasseWalks.HStep}
  {n : ℕ}
-- given
  (hw : WalkTypeCount.IsValidStepWord w n) :
-- imply
  WalkTypeCount.applyStepWord w WalkCountFormula.emptyBasis = WalkTypeCount.downStepProduct w • WalkCountFormula.iterU n WalkCountFormula.emptyBasis := by
-- proof
  open WalkTypeCount in
  rw [applyStepWord_emptyBasis_eq]
  congr 1
  · exact downFactor_zero_eq_downStepProduct w hw.2
  · have hfl := finalLevel_eq_of_valid w 0 (by simpa using hw.2)
    simp only [Nat.cast_zero, zero_add] at hfl; rw [hw.1] at hfl
    have : finalLevel w 0 = n := by exact_mod_cast hfl
    rw [this]
noncomputable section
open HasseWalks

namespace WalkTypeCount

/--
[iterU_emptyBasis_coeff_eq_numSYT](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma iterU_emptyBasis_coeff_eq_numSYT
  {lam : YoungDiagram} :
-- imply
  (WalkCountFormula.iterU lam.card WalkCountFormula.emptyBasis) lam = (HasseWalkFormula.numSYT lam : ℤ) := by
-- proof
  have h1 := HasseWalkFormula.upWalkCount_eq_iterU_apply lam.card lam
  have h2 := HasseWalkFormula.upWalkCount_eq_numSYT lam
  have h2_nat : HasseWalkFormula.upWalkCount lam.card lam = HasseWalkFormula.numSYT lam := by
    exact_mod_cast h2
  rw [← h1]; exact_mod_cast h2_nat

end WalkTypeCount

namespace WalkTypeCount

/--
[walkTypeCount_eq_numSYT_mul_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean)
-/
@[path]
lemma walkTypeCount_eq_numSYT_mul_prod
  {w : List HStep}
  {lam : YoungDiagram}
-- given
  (hw : IsValidStepWord w lam.card) :
-- imply
  (walkTypeCount w lam : ℤ) = (HasseWalkFormula.numSYT lam : ℤ) * downStepProduct w := by
-- proof
  rw [walkTypeCount_eq_applyStepWord_coeff w lam]
  rw [applyStepWord_emptyBasis_eq_downStepProduct_smul_iterU w lam.card hw]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  rw [iterU_emptyBasis_coeff_eq_numSYT]; ring
end WalkTypeCount
end



-- created on 2026-10-23
