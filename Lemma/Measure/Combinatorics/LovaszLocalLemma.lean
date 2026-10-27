import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Probability.Combinatorics.LovaszLocalLemma
open Finset SimpleGraph
open scoped BigOperators
open MathlibExt.Probability.Combinatorics.LovaszLocalLemma


namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[prob_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma prob_nonneg [Fintype Ω] (pmf : Ω → ℝ) (hpmf_nonneg : ∀ ω, 0 ≤ pmf ω)
  (E : Set Ω) :
  0 ≤ prob pmf E := by
  unfold prob
  apply Finset.sum_nonneg
  intro ω _
  by_cases h : ω ∈ E
  · simp only [ite_eq_left h]
    exact hpmf_nonneg ω
  · simp only [ite_eq_right h]
    exact le_rfl

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[prob_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma prob_mono [Fintype Ω] (pmf : Ω → ℝ) (hpmf_nonneg : ∀ ω, 0 ≤ pmf ω)
  {E F : Set Ω} (hEF : E ⊆ F) : prob pmf E ≤ prob pmf F := by
  unfold prob
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : ω ∈ E
  · have hF : ω ∈ F := hEF hE
    simp only [ite_eq_left hE, ite_eq_left hF]
    exact le_rfl
  · simp only [ite_eq_right hE]
    by_cases hF : ω ∈ F
    · simp only [ite_eq_left hF]
      exact hpmf_nonneg ω
    · simp only [ite_eq_right hF]
      exact le_rfl

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[prob_univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma prob_univ [Fintype Ω] (pmf : Ω → ℝ) (hpmf_sum : ∑ ω : Ω, pmf ω = 1) :
  prob pmf Set.univ = 1 := by
  unfold prob
  simp only [Set.mem_univ, ite_true]
  exact hpmf_sum

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[prob_compl_inter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma prob_compl_inter [Fintype Ω] (pmf : Ω → ℝ) (A : I → Set Ω) (i : I) (X :
  Set Ω) :
  prob pmf ((A i)ᶜ ∩ X) = prob pmf X - prob pmf (A i ∩ X) := by
  unfold prob
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hX : ω ∈ X <;> by_cases hA : ω ∈ A i <;>
    simp [Set.mem_inter_iff, Set.mem_compl_iff, hX, hA]

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[goodSet_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma goodSet_empty (A : I → Set Ω) : goodSet A ∅ = Set.univ := by
  ext ω
  simp [goodSet]

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[goodSet_insert](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma goodSet_insert [DecidableEq I] (A : I → Set Ω) (i : I) (S : Finset I) :
  goodSet A (insert i S) = (A i)ᶜ ∩ goodSet A S := by
  ext ω
  simp [goodSet, Set.mem_inter_iff, Set.mem_compl_iff]

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[hDep_setForm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma hDep_setForm [Fintype Ω] [Fintype I] [DecidableEq I] (pmf : Ω → ℝ) (A : I
  → Set Ω) (i : I) (S : Finset I)
  (h : ∑ ω : Ω, (if ω ∈ A i ∧ ∀ j ∈ S, ω ∈ A j then pmf ω else 0) =
    (∑ ω : Ω, (if ω ∈ A i then pmf ω else 0)) *
    (∑ ω : Ω, (if ∀ j ∈ S, ω ∈ A j then pmf ω else 0))) :
  prob pmf (A i ∩ allSet A S) = prob pmf (A i) * prob pmf (allSet A S) := by
  have hiff1 : ∀ ω : Ω, (ω ∈ A i ∩ allSet A S) ↔ (ω ∈ A i ∧ ∀ j ∈ S, ω ∈
    A j) := by
    intro ω
    simp only [Set.mem_inter_iff, allSet, Set.mem_ofPred_eq]
  have hiff2 : ∀ ω : Ω, (ω ∈ allSet A S) ↔ (∀ j ∈ S, ω ∈ A j) := by
    intro ω
    simp only [allSet, Set.mem_ofPred_eq]
  have p1 : prob pmf (A i ∩ allSet A S) =
    (∑ ω : Ω, (if ω ∈ A i ∧ ∀ j ∈ S, ω ∈ A j then pmf ω else 0)) := by
    unfold prob
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h1 : ω ∈ A i ∩ allSet A S
    · rw [ite_eq_left h1, ite_eq_left ((hiff1 ω).mp h1)]
    · rw [ite_eq_right h1, ite_eq_right (fun hh => h1 ((hiff1 ω).mpr hh))]
  have p2 : prob pmf (allSet A S) =
    (∑ ω : Ω, (if ∀ j ∈ S, ω ∈ A j then pmf ω else 0)) := by
    unfold prob
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h2 : ω ∈ allSet A S
    · rw [ite_eq_left h2, ite_eq_left ((hiff2 ω).mp h2)]
    · rw [ite_eq_right h2, ite_eq_right (fun hh => h2 ((hiff2 ω).mpr hh))]
  have p3 : prob pmf (A i) = (∑ ω : Ω, (if ω ∈ A i then pmf ω else 0)) := rfl
  rwa [p1, p3, p2]

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[prod_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma prod_one_sub (N : Finset I) (f : I → ℝ) :
  ∏ j ∈ N, (1 - f j) = ∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * ∏ j ∈ T, f j := by
  have h := Finset.prod_sub (fun _ : I => (1 : ℝ)) f N
  simp only [Finset.prod_const_one, mul_one] at h
  exact h

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[indicator_allSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma indicator_allSet (A : I → Set Ω) (T : Finset I) (ω : Ω) :
  (∏ j ∈ T, (if ω ∈ A j then (1 : ℝ) else 0)) =
    (if ω ∈ allSet A T then 1 else 0) := by
  by_cases hall : ω ∈ allSet A T
  · rw [ite_eq_left hall]
    have h1 : ∀ j ∈ T, (if ω ∈ A j then (1 : ℝ) else 0) = 1 := by
      intro j hj
      have hmem : ω ∈ A j := by
        simp only [allSet, Set.mem_ofPred_eq] at hall
        exact hall j hj
      simp [hmem]
    have hprod : (∏ j ∈ T, (if ω ∈ A j then (1 : ℝ) else 0)) = ∏ j ∈ T, (1 : ℝ) :=
      Finset.prod_congr rfl h1
    rw [hprod, Finset.prod_const_one]
  · rw [ite_eq_right hall]
    simp only [allSet, Set.mem_ofPred_eq] at hall
    push Not at hall
    obtain ⟨j, hj, hnj⟩ := hall
    exact Finset.prod_eq_zero hj (by simp [hnj])

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[indicator_goodSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma indicator_goodSet (A : I → Set Ω) (N : Finset I) (ω : Ω) :
  (if ω ∈ goodSet A N then (1 : ℝ) else 0) =
    ∏ j ∈ N, (1 - (if ω ∈ A j then (1 : ℝ) else 0)) := by
  by_cases hgood : ω ∈ goodSet A N
  · rw [ite_eq_left hgood]
    have h1 : ∀ j ∈ N, (1 - (if ω ∈ A j then (1 : ℝ) else 0)) = 1 := by
      intro j hj
      have hnj : ω ∉ A j := by
        simp only [goodSet, Set.mem_ofPred_eq] at hgood
        exact hgood j hj
      simp [hnj]
    have hprod : (∏ j ∈ N, (1 - (if ω ∈ A j then (1 : ℝ) else 0))) =
      ∏ j ∈ N, (1 : ℝ) :=
      Finset.prod_congr rfl h1
    rw [hprod, Finset.prod_const_one]
  · rw [ite_eq_right hgood]
    simp only [goodSet, Set.mem_ofPred_eq] at hgood
    push Not at hgood
    obtain ⟨j, hj, hmem⟩ := hgood
    have hzero : (1 - (if ω ∈ A j then (1 : ℝ) else 0)) = 0 := by
      simp [hmem]
    exact (Finset.prod_eq_zero hj hzero).symm

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[compl_indep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
the joint with goodSet factors. -/
private lemma compl_indep [Fintype Ω] [Fintype I] [DecidableEq I] (pmf : Ω → ℝ) (A : I
  → Set Ω) (G : SimpleGraph I)
  (i : I) (N : Finset I)
  (hDep : ∀ (i : I) (S : Finset I), (∀ j ∈ S, j ∉ insert i (G.neighborSet i)) →
    ∑ ω : Ω, (if ω ∈ A i ∧ ∀ j ∈ S, ω ∈ A j then pmf ω else 0) =
    (∑ ω : Ω, (if ω ∈ A i then pmf ω else 0)) *
    (∑ ω : Ω, (if ∀ j ∈ S, ω ∈ A j then pmf ω else 0)))
  (hN : ∀ j ∈ N, j ∉ insert i (G.neighborSet i)) :
  prob pmf (A i ∩ goodSet A N) = prob pmf (A i) * prob pmf (goodSet A N) := by
  have hGoodExp : ∀ ω : Ω, (if ω ∈ goodSet A N then (1 : ℝ) else 0) =
    ∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * (if ω ∈ allSet A T then (1 : ℝ) else 0)
      := by
    intro ω
    rw [indicator_goodSet A N ω, prod_one_sub N (fun j => if ω ∈ A j then (1 : ℝ) else 0)]
    apply Finset.sum_congr rfl
    intro T hT
    rw [indicator_allSet A T ω]
  have hInter : prob pmf (A i ∩ goodSet A N) =
    ∑ ω : Ω, pmf ω * ((if ω ∈ A i then (1 : ℝ) else 0) * (if ω ∈ goodSet A N then
      (1 : ℝ) else 0)) := by
    unfold prob
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hA : ω ∈ A i <;> by_cases hG : ω ∈ goodSet A N <;> simp [Set.mem_inter_iff,
      hA, hG]
  have hGoodPmf : prob pmf (goodSet A N) =
    ∑ ω : Ω, pmf ω * (if ω ∈ goodSet A N then (1 : ℝ) else 0) := by
    unfold prob
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hG : ω ∈ goodSet A N <;> simp [hG]
  have hInterT : ∀ T : Finset I, prob pmf (A i ∩ allSet A T) =
    ∑ ω : Ω, pmf ω * ((if ω ∈ A i then (1 : ℝ) else 0) * (if ω ∈ allSet A T then
      (1 : ℝ) else 0)) := by
    intro T
    unfold prob
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hA : ω ∈ A i <;> by_cases hAll : ω ∈ allSet A T <;> simp [Set.mem_inter_iff,
      hA, hAll]
  have hAllPmf : ∀ T : Finset I, prob pmf (allSet A T) =
    ∑ ω : Ω, pmf ω * (if ω ∈ allSet A T then (1 : ℝ) else 0) := by
    intro T
    unfold prob
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hAll : ω ∈ allSet A T <;> simp [hAll]
  have hSub : ∀ T ∈ N.powerset, ∀ j ∈ T, j ∉ insert i (G.neighborSet i) := by
    intro T hT j hj
    have hsub : T ⊆ N := Finset.mem_powerset.mp hT
    exact hN j (hsub hj)
  have hFac : ∀ T ∈ N.powerset, prob pmf (A i ∩ allSet A T) = prob pmf (A i) * prob pmf
    (allSet A T) := by
    intro T hT
    apply hDep_setForm
    exact hDep i T (hSub T hT)
  rw [hInter]
  have hLHS : (∑ ω : Ω, pmf ω * ((if ω ∈ A i then (1 : ℝ) else 0) * (if ω ∈ goodSet
    A N then (1 : ℝ) else 0))) =
    ∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * prob pmf (A i ∩ allSet A T) := by
    calc (∑ ω : Ω, pmf ω * ((if ω ∈ A i then (1 : ℝ) else 0) * (if ω ∈ goodSet A N
      then (1 : ℝ) else 0)))
      = ∑ ω : Ω, ∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * (pmf ω * ((if ω ∈ A i
        then (1 : ℝ) else 0) * (if ω ∈ allSet A T then (1 : ℝ) else 0))) := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [hGoodExp ω]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        ring
      _ = ∑ T ∈ N.powerset, ∑ ω : Ω, ((-1 : ℝ) ^ T.card) * (pmf ω * ((if ω ∈ A i
        then (1 : ℝ) else 0) * (if ω ∈ allSet A T then (1 : ℝ) else 0))) := Finset.sum_comm
      _ = ∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * (∑ ω : Ω, pmf ω * ((if ω ∈ A i
        then (1 : ℝ) else 0) * (if ω ∈ allSet A T then (1 : ℝ) else 0))) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [Finset.mul_sum]
      _ = ∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * prob pmf (A i ∩ allSet A T) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [hInterT T]
  have hRHS : prob pmf (goodSet A N) =
    ∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * prob pmf (allSet A T) := by
    rw [hGoodPmf]
    calc (∑ ω : Ω, pmf ω * (if ω ∈ goodSet A N then (1 : ℝ) else 0))
      = ∑ ω : Ω, ∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * (pmf ω * (if ω ∈ allSet
        A T then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [hGoodExp ω]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        ring
      _ = ∑ T ∈ N.powerset, ∑ ω : Ω, ((-1 : ℝ) ^ T.card) * (pmf ω * (if ω ∈ allSet
        A T then (1 : ℝ) else 0)) := Finset.sum_comm
      _ = ∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * (∑ ω : Ω, pmf ω * (if ω ∈ allSet
        A T then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [Finset.mul_sum]
      _ = ∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * prob pmf (allSet A T) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [hAllPmf T]
  rw [hLHS]
  have hFacSum : (∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * prob pmf (A i ∩ allSet A T)) =
    prob pmf (A i) * (∑ T ∈ N.powerset, ((-1 : ℝ) ^ T.card) * prob pmf (allSet A T)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [hFac T hT]
    ring
  rw [hFacSum, ← hRHS]

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[exp_one_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma exp_one_ge_one : (1 : ℝ) ≤ Real.exp 1 := by
  have h : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
  linarith

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[ep_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma ep_nonneg (p : ℝ) (hp_nonneg : 0 ≤ p) : 0 ≤ Real.exp 1 * p :=
  mul_nonneg (le_of_lt (Real.exp_pos 1)) hp_nonneg

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[p_le_ep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma p_le_ep (p : ℝ) (hp_nonneg : 0 ≤ p) : p ≤ Real.exp 1 * p := by
  calc p = 1 * p := (one_mul p).symm
    _ ≤ Real.exp 1 * p := mul_le_mul_of_nonneg_right exp_one_ge_one hp_nonneg

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[one_sub_ep_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma one_sub_ep_le_one (p : ℝ) (hp_nonneg : 0 ≤ p) : 1 - Real.exp 1 * p ≤ 1 := by
  have h := ep_nonneg p hp_nonneg
  linarith

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[telescope](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma telescope [Fintype Ω] [DecidableEq I] (pmf : Ω → ℝ) (hpmf_nonneg : ∀ ω,
  0 ≤ pmf ω) (A : I → Set Ω)
  (ep : ℝ) (h_nonneg : 0 ≤ 1 - ep) (N D : Finset I)
  (hDisj : Disjoint D N)
  (hpos : ∀ E : Finset I, E ⊆ D → 0 < prob pmf (goodSet A (E ∪ N)))
  (hstep : ∀ (E : Finset I) (j : I), E ⊆ D → j ∈ D → j ∉ E → j ∉ N →
    1 - ep ≤ prob pmf (goodSet A (insert j (E ∪ N))) / prob pmf (goodSet A (E ∪ N))) :
  (1 - ep) ^ D.card ≤ prob pmf (goodSet A (D ∪ N)) / prob pmf (goodSet A N) := by
  revert hDisj hpos hstep
  induction D using Finset.induction with
  | empty =>
    intro hDisj hpos hstep
    have hN : 0 < prob pmf (goodSet A N) := by
      have h := hpos ∅ le_rfl
      simpa [Finset.empty_union] using h
    simp only [Finset.card_empty, pow_zero, Finset.empty_union, div_self (ne_of_gt hN)]
    exact le_rfl
  | insert j E hj ih =>
    intro hDisj hpos hstep
    have hDisjE : Disjoint E N := Disjoint.mono_left (Finset.subset_insert j E) hDisj
    have hjN : j ∉ N := Finset.disjoint_left.mp hDisj (Finset.mem_insert_self j E)
    have hEN_pos : 0 < prob pmf (goodSet A (E ∪ N)) := hpos E (Finset.subset_insert j E)
    have hN_pos : 0 < prob pmf (goodSet A N) := by
      have h := hpos ∅ (Finset.empty_subset _)
      simpa [Finset.empty_union] using h
    have hposE : ∀ E' : Finset I, E' ⊆ E → 0 < prob pmf (goodSet A (E' ∪ N)) := by
      intro E' hsub
      exact hpos E' (Subset.trans hsub (Finset.subset_insert j E))
    have hstepE : ∀ (E' : Finset I) (k : I), E' ⊆ E → k ∈ E → k ∉ E' → k ∉ N →
      1 - ep ≤ prob pmf (goodSet A (insert k (E' ∪ N))) / prob pmf (goodSet A (E' ∪ N))
        := by
      intro E' k hsub hk hne hkN
      exact hstep E' k (Subset.trans hsub (Finset.subset_insert j E))
        (Finset.mem_insert_of_mem hk) hne hkN
    have ih' : (1 - ep) ^ E.card ≤ prob pmf (goodSet A (E ∪ N)) / prob pmf (goodSet A N) :=
      ih hDisjE hposE hstepE
    have hstep_j : 1 - ep ≤ prob pmf (goodSet A (insert j (E ∪ N))) / prob pmf (goodSet A (E
      ∪ N)) :=
      hstep E j (Finset.subset_insert j E) (Finset.mem_insert_self j E) hj hjN
    have h_eq : (insert j E) ∪ N = insert j (E ∪ N) := Finset.insert_union j E N
    have hPEq : prob pmf (goodSet A ((insert j E) ∪ N)) =
      prob pmf (goodSet A (insert j (E ∪ N))) := by rw [h_eq]
    have hb_ne : prob pmf (goodSet A (E ∪ N)) ≠ 0 := ne_of_gt hEN_pos
    have hc_ne : prob pmf (goodSet A N) ≠ 0 := ne_of_gt hN_pos
    have hdiv : prob pmf (goodSet A ((insert j E) ∪ N)) / prob pmf (goodSet A N) =
      (prob pmf (goodSet A (insert j (E ∪ N))) / prob pmf (goodSet A (E ∪ N))) *
      (prob pmf (goodSet A (E ∪ N)) / prob pmf (goodSet A N)) := by
      rw [hPEq]
      field_simp
    rw [hdiv, Finset.card_insert_of_notMem hj, pow_succ']
    have h1 : 0 ≤ (1 - ep) ^ E.card := pow_nonneg h_nonneg E.card
    have h2 : 0 ≤ prob pmf (goodSet A (insert j (E ∪ N))) / prob pmf (goodSet A (E ∪ N)) :=
      div_nonneg (prob_nonneg pmf hpmf_nonneg _) (le_of_lt hEN_pos)
    exact mul_le_mul hstep_j ih' h1 h2

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[main_induction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma main_induction [Fintype Ω] [Fintype I] [DecidableEq I] (pmf : Ω → ℝ)
  (hpmf_nonneg : ∀ ω, 0 ≤ pmf ω)
  (hpmf_sum : ∑ ω : Ω, pmf ω = 1) (A : I → Set Ω) (G : SimpleGraph I) [DecidableRel G.Adj]
  (p : ℝ) (d : ℕ) (hp_nonneg : 0 ≤ p) (hmaxDeg : G.maxDegree ≤ d)
  (hp_le : ∀ i : I, ∑ ω : Ω, (if ω ∈ A i then pmf ω else 0) ≤ p)
  (hDep : ∀ (i : I) (S : Finset I), (∀ j ∈ S, j ∉ insert i (G.neighborSet i)) →
    ∑ ω : Ω, (if ω ∈ A i ∧ ∀ j ∈ S, ω ∈ A j then pmf ω else 0) =
    (∑ ω : Ω, (if ω ∈ A i then pmf ω else 0)) *
    (∑ ω : Ω, (if ∀ j ∈ S, ω ∈ A j then pmf ω else 0)))
  (hPos : 0 < 1 - Real.exp 1 * p)
  (hPow : (1 : ℝ) / Real.exp 1 ≤ (1 - Real.exp 1 * p) ^ d) :
  ∀ (n : ℕ) (S : Finset I), S.card ≤ n →
    (1 - Real.exp 1 * p) ^ S.card ≤ prob pmf (goodSet A S) ∧
    (∀ i₀ : I, i₀ ∉ S → prob pmf (A i₀ ∩ goodSet A S) / prob pmf (goodSet A S)
      ≤ Real.exp 1 * p) := by
  intro n
  induction n with
  | zero =>
    intro S hcard
    have hcard0 : S.card = 0 := by omega
    have hS_empty : S = ∅ := Finset.card_eq_zero.mp hcard0
    subst hS_empty
    constructor
    · have hP1 : prob pmf (goodSet A ∅) = 1 := by
      rw [goodSet_empty A, prob_univ pmf hpmf_sum]
      rw [hP1]
      simp only [Finset.card_empty, pow_zero]
      exact le_rfl
    · intro i₀ hi₀
      have hP1 : prob pmf (goodSet A ∅) = 1 := by
        rw [goodSet_empty A, prob_univ pmf hpmf_sum]
      have hInter : A i₀ ∩ goodSet A ∅ = A i₀ := by
        rw [goodSet_empty A, Set.inter_univ]
      rw [hInter, hP1, div_one]
      have hAi0 : prob pmf (A i₀) ≤ p := hp_le i₀
      calc prob pmf (A i₀) ≤ p := hAi0
        _ ≤ Real.exp 1 * p := p_le_ep p hp_nonneg
  | succ n ih =>
    intro S hcard
    by_cases hle : S.card ≤ n
    · exact ih S hle
    · have hcard_eq : S.card = n + 1 := by omega
      have hpos_card : 0 < S.card := by omega
      have hne : S.Nonempty := Finset.card_pos.mp hpos_card
      obtain ⟨i, hi⟩ := hne
      set S' := S.erase i with hS'_def
      have hi'_mem : i ∉ S' := by simp [hS'_def, Finset.mem_erase]
      have hS_eq : S = insert i S' := by
        rw [hS'_def]
        exact (Finset.insert_erase hi).symm
      have hcard_S' : S'.card = n := by
        have h1 : S'.card = S.card - 1 := by
          rw [hS'_def]
          exact Finset.card_erase_of_mem hi
        omega
      have hle_S' : S'.card ≤ n := le_of_eq hcard_S'
      have ih_S' := ih S' hle_S'
      have h_uncond : (1 - Real.exp 1 * p) ^ S.card ≤ prob pmf (goodSet A S) := by
        have h1 : (1 - Real.exp 1 * p) ^ S'.card ≤ prob pmf (goodSet A S') := ih_S'.1
        have hpow_pos : 0 < (1 - Real.exp 1 * p) ^ S'.card := pow_pos hPos S'.card
        have hS'_pos : 0 < prob pmf (goodSet A S') := lt_of_lt_of_le hpow_pos h1
        have hcond_i : prob pmf (A i ∩ goodSet A S') / prob pmf (goodSet A S') ≤ Real.exp 1
          * p :=
          ih_S'.2 i hi'_mem
        have hS'_ne : prob pmf (goodSet A S') ≠ 0 := ne_of_gt hS'_pos
        have hPS_eq : prob pmf (goodSet A S) = prob pmf (goodSet A S') - prob pmf (A i ∩
          goodSet A S') := by
          rw [hS_eq, goodSet_insert, prob_compl_inter]
        have hPS_mul : prob pmf (goodSet A S) =
          prob pmf (goodSet A S') * (1 - prob pmf (A i ∩ goodSet A S') / prob pmf (goodSet A
            S')) := by
          rw [hPS_eq]
          field_simp
        have h1ep_le : 1 - Real.exp 1 * p ≤ 1 - prob pmf (A i ∩ goodSet A S') / prob pmf
          (goodSet A S') := by
          linarith [hcond_i]
        have h_nonneg_ep : 0 ≤ 1 - Real.exp 1 * p := le_of_lt hPos
        have h_nonneg_P : 0 ≤ prob pmf (goodSet A S') := prob_nonneg pmf hpmf_nonneg _
        have hcard_eq2 : S.card = S'.card + 1 := by omega
        have hpow_eq : (1 - Real.exp 1 * p) ^ S.card =
          (1 - Real.exp 1 * p) ^ S'.card * (1 - Real.exp 1 * p) := by
          rw [hcard_eq2, pow_succ]
        rw [hpow_eq, hPS_mul]
        exact mul_le_mul h1 h1ep_le h_nonneg_ep h_nonneg_P
      have h_cond : ∀ i₀ : I, i₀ ∉ S →
        prob pmf (A i₀ ∩ goodSet A S) / prob pmf (goodSet A S) ≤ Real.exp 1 * p := by
        intro i₀ hi₀
        set D := S.filter (fun j => j ∈ G.neighborSet i₀) with hD_def
        set N := S \ D with hN_def
        have hD_sub_S : D ⊆ S := by
          rw [hD_def]
          exact Finset.filter_subset _ _
        have hN_sub_S : N ⊆ S := by
          rwa [hN_def]
        have h_union : D ∪ N = S := by
          rw [hN_def]
          exact Finset.union_sdiff_of_subset hD_sub_S
        have hDisj : Disjoint D N := by
          rw [hN_def]
          apply Finset.disjoint_left.mpr
          intro x hxD hxSD
          rw [Finset.mem_sdiff] at hxSD
          exact hxSD.2 hxD
        have hD_le_d : D.card ≤ d := by
          have hD_sub_nf : D ⊆ G.neighborFinset i₀ := by
            intro j hj
            simp only [hD_def, Finset.mem_filter] at hj
            rw [G.mem_neighborFinset]
            have hj2 : j ∈ G.neighborSet i₀ := hj.2
            rwa [G.mem_neighborSet] at hj2
          have h1 : D.card ≤ (G.neighborFinset i₀).card := Finset.card_le_card hD_sub_nf
          have h2 : (G.neighborFinset i₀).card = G.degree i₀ := rfl
          have h3 : G.degree i₀ ≤ G.maxDegree := G.degree_le_maxDegree i₀
          omega
        have hS_pos : 0 < prob pmf (goodSet A S) := by
          have hle := h_uncond
          have hpos_pow : 0 < (1 - Real.exp 1 * p) ^ S.card := pow_pos hPos S.card
          exact lt_of_lt_of_le hpos_pow hle
        have hS_ne : prob pmf (goodSet A S) ≠ 0 := ne_of_gt hS_pos
        have hN_avoid : ∀ j ∈ N, j ∉ insert i₀ (G.neighborSet i₀) := by
          intro j hjN
          rw [hN_def, Finset.mem_sdiff] at hjN
          obtain ⟨hjS, hj_notD⟩ := hjN
          have hj_ne : j ≠ i₀ := by
            intro heq
            subst heq
            exact hi₀ hjS
          have hj_nnb : j ∉ G.neighborSet i₀ := by
            intro hmem
            have hDmem : j ∈ D := by
              rw [hD_def, Finset.mem_filter]
              exact ⟨hjS, hmem⟩
            exact hj_notD hDmem
          simp [Set.mem_insert_iff, hj_ne, hj_nnb]
        have h_good_sub : goodSet A S ⊆ goodSet A N := by
          intro ω hω
          simp only [goodSet, Set.mem_ofPred_eq] at hω ⊢
          intro j hjN
          exact hω j (hN_sub_S hjN)
        have h_inter_sub : A i₀ ∩ goodSet A S ⊆ A i₀ ∩ goodSet A N := by
          intro ω hω
          simp only [Set.mem_inter_iff] at hω ⊢
          exact ⟨hω.1, h_good_sub hω.2⟩
        have h_num_le : prob pmf (A i₀ ∩ goodSet A S) ≤ prob pmf (A i₀ ∩ goodSet A N) :=
          prob_mono pmf hpmf_nonneg h_inter_sub
        have h_step0 : prob pmf (A i₀ ∩ goodSet A N) =
          prob pmf (A i₀) * prob pmf (goodSet A N) :=
          compl_indep pmf A G i₀ N hDep hN_avoid
        have hAi0_le : prob pmf (A i₀) ≤ p := hp_le i₀
        have hPN_nonneg : 0 ≤ prob pmf (goodSet A N) := prob_nonneg pmf hpmf_nonneg _
        have h_num_le2 : prob pmf (A i₀ ∩ goodSet A S) ≤ p * prob pmf (goodSet A N) := by
          calc prob pmf (A i₀ ∩ goodSet A S) ≤ prob pmf (A i₀ ∩ goodSet A N) := h_num_le
            _ = prob pmf (A i₀) * prob pmf (goodSet A N) := h_step0
            _ ≤ p * prob pmf (goodSet A N) := mul_le_mul_of_nonneg_right hAi0_le hPN_nonneg
        have hN_pos : 0 < prob pmf (goodSet A N) := by
          have hle : prob pmf (goodSet A S) ≤ prob pmf (goodSet A N) :=
            prob_mono pmf hpmf_nonneg h_good_sub
          exact lt_of_lt_of_le hS_pos hle
        have hN_ne : prob pmf (goodSet A N) ≠ 0 := ne_of_gt hN_pos
        have h_cond_le : prob pmf (A i₀ ∩ goodSet A S) / prob pmf (goodSet A S) ≤
          p * prob pmf (goodSet A N) / prob pmf (goodSet A S) := by
          have h_inv : 0 ≤ (prob pmf (goodSet A S))⁻¹ := inv_nonneg.mpr (le_of_lt hS_pos)
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right h_num_le2 h_inv
        have h_eq : p * prob pmf (goodSet A N) / prob pmf (goodSet A S) =
          p / (prob pmf (goodSet A S) / prob pmf (goodSet A N)) := by
          field_simp
        have h0 : prob pmf (A i₀ ∩ goodSet A S) / prob pmf (goodSet A S) ≤
          p / (prob pmf (goodSet A S) / prob pmf (goodSet A N)) := by
          rwa [← h_eq]
        have h_tel_pos : ∀ E : Finset I, E ⊆ D → 0 < prob pmf (goodSet A (E ∪ N)) := by
          intro E hsub
          have h1 : E ∪ N ⊆ D ∪ N := Finset.union_subset_union hsub (Subset.rfl)
          rw [h_union] at h1
          have hgood_sub2 : goodSet A S ⊆ goodSet A (E ∪ N) := by
            intro ω hω
            simp only [goodSet, Set.mem_ofPred_eq] at hω ⊢
            intro j hj
            exact hω j (h1 hj)
          have hle : prob pmf (goodSet A S) ≤ prob pmf (goodSet A (E ∪ N)) :=
            prob_mono pmf hpmf_nonneg hgood_sub2
          exact lt_of_lt_of_le hS_pos hle
        have h_tel_step : ∀ (E : Finset I) (j : I), E ⊆ D → j ∈ D → j ∉ E → j ∉
          N →
          1 - Real.exp 1 * p ≤ prob pmf (goodSet A (insert j (E ∪ N))) / prob pmf (goodSet
            A (E ∪ N)) := by
          intro E j hsub hjD hjE hjN
          set S' := E ∪ N with hS'_def
          have hsub_S : S' ⊆ S := by
            have h1 : E ∪ N ⊆ D ∪ N := Finset.union_subset_union hsub (Subset.rfl)
            rw [h_union] at h1
            rwa [hS'_def]
          have hjS : j ∈ S := hD_sub_S hjD
          have hj_notS' : j ∉ S' := by
            rw [hS'_def, Finset.mem_union]
            simp [hjE, hjN]
          have hsub_insert : insert j S' ⊆ S := Finset.insert_subset hjS hsub_S
          have hcard_le : (insert j S').card ≤ S.card := Finset.card_le_card hsub_insert
          have hcard_ins : (insert j S').card = S'.card + 1 := Finset.card_insert_of_notMem hj_notS'
          have hle_n : S'.card ≤ n := by omega
          have ih_S' := ih S' hle_n
          have hcond : prob pmf (A j ∩ goodSet A S') / prob pmf (goodSet A S') ≤ Real.exp 1
            * p :=
            ih_S'.2 j hj_notS'
          have hS'_pos : 0 < prob pmf (goodSet A S') := by
            rw [hS'_def]
            exact h_tel_pos E hsub
          have hS'_ne : prob pmf (goodSet A S') ≠ 0 := ne_of_gt hS'_pos
          have hP_eq : prob pmf (goodSet A (insert j S')) =
            prob pmf (goodSet A S') - prob pmf (A j ∩ goodSet A S') := by
            rw [goodSet_insert, prob_compl_inter]
          have hP_mul : prob pmf (goodSet A (insert j S')) =
            prob pmf (goodSet A S') * (1 - prob pmf (A j ∩ goodSet A S') / prob pmf (goodSet
              A S')) := by
            rw [hP_eq]
            field_simp
          have hdiv_eq : prob pmf (goodSet A (insert j S')) / prob pmf (goodSet A S') =
            1 - prob pmf (A j ∩ goodSet A S') / prob pmf (goodSet A S') := by
            rw [hP_mul]
            field_simp
          rw [hdiv_eq]
          linarith [hcond]
        have h_tel := telescope pmf hpmf_nonneg A (Real.exp 1 * p) (le_of_lt hPos) N D hDisj
          h_tel_pos h_tel_step
        have h_ratio_ge : (1 - Real.exp 1 * p) ^ D.card ≤
          prob pmf (goodSet A S) / prob pmf (goodSet A N) := by
          have h := h_tel
          rwa [h_union] at h
        have h_powD_pos : 0 < (1 - Real.exp 1 * p) ^ D.card := pow_pos hPos D.card
        have h1 : p / (prob pmf (goodSet A S) / prob pmf (goodSet A N)) ≤
          p / (1 - Real.exp 1 * p) ^ D.card := by
          exact div_le_div_of_nonneg_left hp_nonneg h_powD_pos h_ratio_ge
        have h_powd_pos : 0 < (1 - Real.exp 1 * p) ^ d := pow_pos hPos d
        have h_pow_le : (1 - Real.exp 1 * p) ^ d ≤ (1 - Real.exp 1 * p) ^ D.card := by
          exact pow_le_pow_of_le_one (le_of_lt hPos) (one_sub_ep_le_one p hp_nonneg) hD_le_d
        have h2 : p / (1 - Real.exp 1 * p) ^ D.card ≤ p / (1 - Real.exp 1 * p) ^ d := by
          exact div_le_div_of_nonneg_left hp_nonneg h_powd_pos h_pow_le
        have h3 : p / (1 - Real.exp 1 * p) ^ d ≤ Real.exp 1 * p := by
          by_cases hp0 : p = 0
          · subst hp0
            simp
          · have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp0)
            have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
            rw [div_le_iff₀ h_powd_pos]
            have h1e : (1 : ℝ) ≤ Real.exp 1 * (1 - Real.exp 1 * p) ^ d := by
              have h := hPow
              rw [div_le_iff₀ he_pos] at h
              rwa [mul_comm] at h
            calc p = p * 1 := (mul_one p).symm
              _ ≤ p * (Real.exp 1 * (1 - Real.exp 1 * p) ^ d) := mul_le_mul_of_nonneg_left h1e
                hp_nonneg
              _ = Real.exp 1 * p * (1 - Real.exp 1 * p) ^ d := by ring
        calc prob pmf (A i₀ ∩ goodSet A S) / prob pmf (goodSet A S)
          ≤ p / (prob pmf (goodSet A S) / prob pmf (goodSet A N)) := h0
          _ ≤ p / (1 - Real.exp 1 * p) ^ D.card := h1
          _ ≤ p / (1 - Real.exp 1 * p) ^ d := h2
          _ ≤ Real.exp 1 * p := h3
      exact ⟨h_uncond, h_cond⟩

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[exp_pow_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma exp_pow_le (p : ℝ) (d : ℕ)
  (hExp : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1)
  (hPos : 0 < 1 - Real.exp 1 * p) :
  (1 : ℝ) / Real.exp 1 ≤ (1 - Real.exp 1 * p) ^ d := by
  have hne : (1 : ℝ) - Real.exp 1 * p ≠ 0 := ne_of_gt hPos
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  set y := Real.exp 1 * p / (1 - Real.exp 1 * p) with hy_def
  have h_add : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have h_one_div : (1 : ℝ) / (1 - Real.exp 1 * p) ≤ Real.exp y := by
    have heq : y + 1 = 1 / (1 - Real.exp 1 * p) := by
      rw [hy_def]
      field_simp
      ring
    rwa [heq] at h_add
  have h_a_pos : 0 < (1 : ℝ) / (1 - Real.exp 1 * p) := div_pos zero_lt_one hPos
  have h_inv_le : (1 : ℝ) / Real.exp y ≤ 1 - Real.exp 1 * p := by
    have h1 : (1 : ℝ) / Real.exp y ≤ 1 / (1 / (1 - Real.exp 1 * p)) :=
      div_le_div_of_nonneg_left zero_le_one h_a_pos h_one_div
    have heq2 : (1 : ℝ) / (1 / (1 - Real.exp 1 * p)) = 1 - Real.exp 1 * p := by
      field_simp
    rwa [heq2] at h1
  have h_exp_neg : Real.exp (-y) ≤ 1 - Real.exp 1 * p := by
    have heq3 : (1 : ℝ) / Real.exp y = Real.exp (-y) := by
      rw [Real.exp_neg, one_div]
    rwa [heq3] at h_inv_le
  have h_exp_nonneg : 0 ≤ Real.exp (-y) := le_of_lt (Real.exp_pos _)
  have h_pow_le : Real.exp (-y) ^ d ≤ (1 - Real.exp 1 * p) ^ d :=
    pow_le_pow_left₀ h_exp_nonneg h_exp_neg d
  have h_exp_pow_eq : Real.exp (-y) ^ d = Real.exp (-(Real.exp 1 * p * (d : ℝ) / (1 - Real.exp
    1 * p))) := by
    have h1 : Real.exp (-y) ^ d = Real.exp ((d : ℝ) * (-y)) := (Real.exp_nat_mul (-y) d).symm
    have hexp_eq : (d : ℝ) * (-y) = -(Real.exp 1 * p * (d : ℝ) / (1 - Real.exp 1 * p)) := by
      rw [hy_def]
      field_simp
    rw [h1, hexp_eq]
  have h_epd : Real.exp 1 * p * (d : ℝ) ≤ 1 - Real.exp 1 * p := by
    have heq : Real.exp 1 * p * ((d : ℝ) + 1) = Real.exp 1 * p * (d : ℝ) + Real.exp 1 * p :=
      by ring
    linarith [hExp]
  have h_div_le : Real.exp 1 * p * (d : ℝ) / (1 - Real.exp 1 * p) ≤ 1 := by
    rw [div_le_iff₀ hPos]
    simp only [one_mul]
    exact h_epd
  have h_neg : (-1 : ℝ) ≤ -(Real.exp 1 * p * (d : ℝ) / (1 - Real.exp 1 * p)) := by
    linarith [h_div_le]
  have h_exp_mono : Real.exp (-1) ≤ Real.exp (-(Real.exp 1 * p * (d : ℝ) / (1 - Real.exp 1 *
    p))) :=
    Real.exp_le_exp.mpr h_neg
  have h_exp_neg1 : Real.exp (-1) = 1 / Real.exp 1 := by
    rw [Real.exp_neg, one_div]
  calc (1 : ℝ) / Real.exp 1 = Real.exp (-1) := h_exp_neg1.symm
    _ ≤ Real.exp (-(Real.exp 1 * p * (d : ℝ) / (1 - Real.exp 1 * p))) := h_exp_mono
    _ = Real.exp (-y) ^ d := h_exp_pow_eq.symm
    _ ≤ (1 - Real.exp 1 * p) ^ d := h_pow_le

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*}
/--
[special_case](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma special_case [Fintype Ω] [Fintype I] [DecidableEq I] (pmf : Ω → ℝ)
  (hpmf_sum : ∑ ω : Ω, pmf ω = 1) (A : I → Set Ω) (G : SimpleGraph I) [DecidableRel G.Adj]
  (p : ℝ) (d : ℕ) (hp_nonneg : 0 ≤ p) (hmaxDeg : G.maxDegree ≤ d)
  (hp_le : ∀ i : I, ∑ ω : Ω, (if ω ∈ A i then pmf ω else 0) ≤ p)
  (hDep : ∀ (i : I) (S : Finset I), (∀ j ∈ S, j ∉ insert i (G.neighborSet i)) →
    ∑ ω : Ω, (if ω ∈ A i ∧ ∀ j ∈ S, ω ∈ A j then pmf ω else 0) =
    (∑ ω : Ω, (if ω ∈ A i then pmf ω else 0)) *
    (∑ ω : Ω, (if ∀ j ∈ S, ω ∈ A j then pmf ω else 0)))
  (hd0 : d = 0) (hep1 : Real.exp 1 * p = 1) :
  0 < ∑ ω : Ω, (if ∀ i : I, ω ∉ A i then pmf ω else 0) := by
  have hmax0 : G.maxDegree ≤ 0 := by omega
  have h_eq : ∀ S : Finset I, prob pmf (goodSet A S) = ∏ i ∈ S, (1 - prob pmf (A i)) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      rw [goodSet_empty A, prob_univ pmf hpmf_sum]
      simp
    | insert i S' hi ih =>
      have hdeg0 : G.degree i = 0 := by
        have h3 : G.degree i ≤ G.maxDegree := G.degree_le_maxDegree i
        omega
      have hnf_empty : G.neighborFinset i = ∅ := by
        apply Finset.card_eq_zero.mp
        have hcard : (G.neighborFinset i).card = 0 := hdeg0
        exact hcard
      have h_avoid : ∀ j ∈ S', j ∉ insert i (G.neighborSet i) := by
        intro j hj
        have hj_ne : j ≠ i := by
          intro heq
          subst heq
          exact hi hj
        have hj_nnf : j ∉ G.neighborFinset i := by
          rw [hnf_empty]
          simp
        have hj_nnb : j ∉ G.neighborSet i := by
          intro hmem
          have h1 : G.Adj i j := by rwa [G.mem_neighborSet] at hmem
          have h2 : j ∈ G.neighborFinset i := by rwa [G.mem_neighborFinset]
          exact hj_nnf h2
        simp [Set.mem_insert_iff, hj_ne, hj_nnb]
      have h_step0 : prob pmf (A i ∩ goodSet A S') =
        prob pmf (A i) * prob pmf (goodSet A S') :=
        compl_indep pmf A G i S' hDep h_avoid
      have hP_insert : prob pmf (goodSet A (insert i S')) =
        prob pmf (goodSet A S') * (1 - prob pmf (A i)) := by
        rw [goodSet_insert, prob_compl_inter, h_step0]
        ring
      rw [hP_insert, ih, Finset.prod_insert hi]
      ring
  have he_ge2 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith
  have h2p_le1 : 2 * p ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right he_ge2 hp_nonneg
    rwa [hep1] at h
  have hp_lt1 : p < 1 := by linarith [h2p_le1]
  have h_pos_univ : 0 < prob pmf (goodSet A (Finset.univ : Finset I)) := by
    rw [h_eq]
    apply Finset.prod_pos
    intro i hi
    have hAi_le : prob pmf (A i) ≤ p := hp_le i
    linarith [hAi_le, hp_lt1]
  have h_concl : (∑ ω : Ω, (if ∀ i : I, ω ∉ A i then pmf ω else 0)) =
    prob pmf (goodSet A (Finset.univ : Finset I)) := by
    unfold prob
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ∀ i : I, ω ∉ A i
    · have hmem : ω ∈ goodSet A (Finset.univ : Finset I) := by
      simp only [goodSet, Set.mem_ofPred_eq, Finset.mem_univ, true_imp_iff] at h ⊢
      exact h
      rw [ite_eq_left h, ite_eq_left hmem]
    · have hmem : ω ∉ goodSet A (Finset.univ : Finset I) := by
      simp only [goodSet, Set.mem_ofPred_eq, Finset.mem_univ, true_imp_iff] at h ⊢
      exact h
      rw [ite_eq_right h, ite_eq_right hmem]
  rwa [h_concl]

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

/--
[lovasz_local_lemma_symmetric_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
lemma lovasz_local_lemma_symmetric_finite
  [Fintype Ω] [Fintype I] [DecidableEq I]
  {pmf : Ω → ℝ}
  {A : I → Set Ω}
  {G : SimpleGraph I} [DecidableRel G.Adj]
  {p : ℝ}
  {d : ℕ}
-- given
  (hpmf_nonneg : ∀ ω, 0 ≤ pmf ω)
  (hpmf_sum : ∑ ω : Ω, pmf ω = 1)
  (hp_nonneg : 0 ≤ p)
  (hmaxDeg : G.maxDegree ≤ d)
  (hp_le : ∀ i : I, ∑ ω : Ω, (if ω ∈ A i then pmf ω else 0) ≤ p)
  (hDep : ∀ (i : I) (S : Finset I), (∀ j ∈ S, j ∉ insert i (G.neighborSet i)) → ∑ ω : Ω, (if ω ∈ A i ∧ ∀ j ∈ S, ω ∈ A j then pmf ω else 0) = (∑ ω : Ω, (if ω ∈ A i then pmf ω else 0)) * (∑ ω : Ω, (if ∀ j ∈ S, ω ∈ A j then pmf ω else 0)))
  (hExp : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) :
-- imply
  0 < ∑ ω : Ω, (if ∀ i : I, ω ∉ A i then pmf ω else 0) := by
-- proof
  by_cases hspec : d = 0 ∧ Real.exp 1 * p = 1
  · obtain ⟨hd0, hep1⟩ := hspec
    exact special_case pmf hpmf_sum A G p d hp_nonneg hmaxDeg hp_le hDep hd0 hep1
  · have hPos : 0 < 1 - Real.exp 1 * p := by
    by_cases hd0 : d = 0
    · have hep_ne : Real.exp 1 * p ≠ 1 := by
      intro heq
      exact hspec ⟨hd0, heq⟩
      have hep_le : Real.exp 1 * p ≤ 1 := by
        have h := hExp
        rw [hd0] at h
        simpa using h
      have hlt : Real.exp 1 * p < 1 := lt_of_le_of_ne hep_le hep_ne
      linarith
    · have hd_ge1 : 1 ≤ d := by omega
      have hdR : (1 : ℝ) ≤ (d : ℝ) := by
        have h : ((1 : ℕ) : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hd_ge1
        simpa using h
      have h_d1_ge2 : (2 : ℝ) ≤ (d : ℝ) + 1 := by linarith [hdR]
      have h_ep2_le : Real.exp 1 * p * 2 ≤ 1 := by
        have h1 : Real.exp 1 * p * 2 ≤ Real.exp 1 * p * ((d : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h_d1_ge2 (ep_nonneg p hp_nonneg)
        exact le_trans h1 hExp
      have hlt : Real.exp 1 * p < 1 := by linarith [h_ep2_le]
      linarith
    have hPow : (1 : ℝ) / Real.exp 1 ≤ (1 - Real.exp 1 * p) ^ d :=
      exp_pow_le p d hExp hPos
    have hmain := main_induction pmf hpmf_nonneg hpmf_sum A G p d hp_nonneg hmaxDeg hp_le hDep
      hPos hPow
    have hClaim := hmain (Finset.univ : Finset I).card (Finset.univ : Finset I) le_rfl
    have hpos_pow : 0 < (1 - Real.exp 1 * p) ^ (Finset.univ : Finset I).card := pow_pos hPos _
    have hS_pos : 0 < prob pmf (goodSet A (Finset.univ : Finset I)) := lt_of_lt_of_le hpos_pow
      hClaim.1
    have h_concl : (∑ ω : Ω, (if ∀ i : I, ω ∉ A i then pmf ω else 0)) =
      prob pmf (goodSet A (Finset.univ : Finset I)) := by
      unfold prob
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : ∀ i : I, ω ∉ A i
      · have hmem : ω ∈ goodSet A (Finset.univ : Finset I) := by
        simp only [goodSet, Set.mem_ofPred_eq, Finset.mem_univ, true_imp_iff] at h ⊢
        exact h
        rw [ite_eq_left h, ite_eq_left hmem]
      · have hmem : ω ∉ goodSet A (Finset.univ : Finset I) := by
        simp only [goodSet, Set.mem_ofPred_eq, Finset.mem_univ, true_imp_iff] at h ⊢
        exact h
        rw [ite_eq_right h, ite_eq_right hmem]
    rwa [h_concl]

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma


-- created on 2026-10-20
-- updated on 2026-10-26
