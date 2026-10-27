import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Entropy
open Finset Real ShannonEntropy


namespace ShannonEntropy

/--
[pmf_sum_toReal_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma pmf_sum_toReal_eq_one
  [Fintype T]
  {q : PMF T} :
-- imply
  ∑ t : T, (q t).toReal = 1 := by
-- proof
  have hne : ∀ t ∈ (univ : Finset T), (q t) ≠ ⊤ := fun t _ => PMF.apply_ne_top q t
  rw [← ENNReal.toReal_sum hne]
  have h : ∑ t ∈ (univ : Finset T), q t = 1 := by
    have := PMF.tsum_coe q; rwa [tsum_fintype] at this
  rw [h]
  simp

end ShannonEntropy

namespace ShannonEntropy

/--
[pmf_map_snd_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma pmf_map_snd_apply
  [Fintype S]
  [Fintype T]
  [DecidableEq T]
  {p : PMF (S × T)}
  {t : T} :
-- imply
  (PMF.map Prod.snd p) t = ∑ s : S, p (s, t) := by
-- proof
  rw [PMF.map_apply, tsum_fintype]
  conv_lhs => rw [show (univ : Finset (S × T)) = univ ×ˢ univ from (univ_product_univ).symm]
  rw [Finset.sum_product]
  congr 1
  ext s
  simp_rw [eq_comm (a := t)]
  exact Fintype.sum_ite_eq' t (fun x => p (s, x))

end ShannonEntropy

namespace ShannonEntropy

/--
[pmf_map_fst_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma pmf_map_fst_apply
  [Fintype S]
  [Fintype T]
  [DecidableEq S]
  {p : PMF (S × T)}
  {s : S} :
-- imply
  (PMF.map Prod.fst p) s = ∑ t : T, p (s, t) := by
-- proof
  rw [PMF.map_apply, tsum_fintype]
  conv_lhs => rw [show (univ : Finset (S × T)) = univ ×ˢ univ from (univ_product_univ).symm]
  rw [Finset.sum_product_right]
  congr 1
  ext t
  simp_rw [eq_comm (a := s)]
  exact Fintype.sum_ite_eq' s (fun x => p (x, t))

end ShannonEntropy

namespace ShannonEntropy

/--
[pmf_le_map_snd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma pmf_le_map_snd
  [Fintype S]
  [Fintype T]
  [DecidableEq T]
  {p : PMF (S × T)}
  {s : S}
  {t : T} :
-- imply
  p (s, t) ≤ (PMF.map Prod.snd p) t := by
-- proof
  rw [pmf_map_snd_apply]
  exact Finset.single_le_sum (f := fun s => p (s, t)) (fun _ _ => zero_le _) (mem_univ s)

end ShannonEntropy

namespace ShannonEntropy

/--
[total_prob_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma total_prob_toReal
  [Fintype S]
  [Fintype T]
  [DecidableEq S]
  [DecidableEq T]
  {p : PMF (S × T)}
  {s : S} :
-- imply
  ∑ t : T, ((PMF.map Prod.snd p) t).toReal * ((p (s, t)).toReal / ((PMF.map Prod.snd p) t).toReal) = ((PMF.map Prod.fst p) s).toReal := by
-- proof
  have key : ∀ t : T, ((PMF.map Prod.snd p) t).toReal *
    ((p (s, t)).toReal / ((PMF.map Prod.snd p) t).toReal) = (p (s, t)).toReal := by
    intro t
    by_cases ht : ((PMF.map Prod.snd p) t) = 0
    · have hst : p (s, t) = 0 := le_antisymm (ht ▸ pmf_le_map_snd p s t) (zero_le _)
      simp [ht, hst]
    · exact mul_div_cancel₀ _ (ENNReal.toReal_ne_zero.mpr ⟨ht, PMF.apply_ne_top _ t⟩)
  simp_rw [key]
  rw [pmf_map_fst_apply, ENNReal.toReal_sum (fun t _ => PMF.apply_ne_top p (s, t))]

end ShannonEntropy

namespace ShannonEntropy

/--
[entropy_of_independent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma entropy_of_independent
  [Fintype S]
  [Fintype T]
  [DecidableEq S]
  [DecidableEq T]
  {p : PMF (S × T)}
-- given
  (hindep : ∀ s t, p (s, t) = (PMF.map Prod.fst p) s * (PMF.map Prod.snd p) t) :
-- imply
  shannonEntropy p = shannonEntropy (PMF.map Prod.fst p) + shannonEntropy (PMF.map Prod.snd p) := by
-- proof
  simp only [shannonEntropy]
  rw [Fintype.sum_prod_type_right]
  have key : ∀ t s, negMulLog (p (s, t)).toReal =
    (PMF.map Prod.snd p t).toReal * negMulLog (PMF.map Prod.fst p s).toReal +
    (PMF.map Prod.fst p s).toReal * negMulLog (PMF.map Prod.snd p t).toReal := by
    intro t s
    rw [hindep s t, ENNReal.toReal_mul, negMulLog_mul]
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hfst : ∑ s : S, (PMF.map Prod.fst p s).toReal = 1 :=
    pmf_sum_toReal_eq_one (PMF.map Prod.fst p)
  have hsnd : ∑ t : T, (PMF.map Prod.snd p t).toReal = 1 :=
    pmf_sum_toReal_eq_one (PMF.map Prod.snd p)
  rw [hsnd, hfst, one_mul]
  simp_rw [one_mul]

end ShannonEntropy

namespace ShannonEntropy

/--
[sum_toReal_eq_margY_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma sum_toReal_eq_margY_toReal
  [Fintype S]
  [Fintype T]
  [DecidableEq T]
  {p : PMF (S × T)}
  {t : T} :
-- imply
  ∑ s : S, (p (s, t)).toReal = ((PMF.map Prod.snd p) t).toReal := by
-- proof
  rw [pmf_map_snd_apply]
  rw [← ENNReal.toReal_sum (fun s _ => PMF.apply_ne_top p (s, t))]

end ShannonEntropy

namespace ShannonEntropy

/--
[joint_eq_zero_of_margY_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma joint_eq_zero_of_margY_zero
  [Fintype S]
  [Fintype T]
  [DecidableEq T]
  {p : PMF (S × T)}
  {t : T}
  {s : S}
-- given
  (ht : (PMF.map Prod.snd p) t = 0) :
-- imply
  p (s, t) = 0 :=
-- proof
  le_antisymm (ht ▸ pmf_le_map_snd p s t) (zero_le _)

end ShannonEntropy

namespace ShannonEntropy

/--
[entropy_chain_rule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma entropy_chain_rule
  [Fintype S]
  [Fintype T]
  [DecidableEq T]
  {p : PMF (S × T)} :
-- imply
  shannonEntropy p = shannonEntropy (PMF.map Prod.snd p) + conditionalEntropy p := by
-- proof
  simp only [shannonEntropy, conditionalEntropy]
  set margY := PMF.map Prod.snd p
  rw [Fintype.sum_prod_type_right (fun st => negMulLog (p st).toReal)]
  suffices h : ∀ t : T,
    ∑ s : S, negMulLog (p (s, t)).toReal =
      negMulLog (margY t).toReal +
      (margY t).toReal * ∑ s : S, negMulLog ((p (s, t)).toReal / (margY t).toReal) by
    simp_rw [h, ← Finset.sum_add_distrib]
  intro t
  by_cases ht : margY t = 0
  ·
    have hst : ∀ s, (p (s, t)).toReal = 0 := by
      intro s
      have h0 := joint_eq_zero_of_margY_zero p t ht s
      simp [h0]
    have ht_real : (margY t).toReal = 0 := by simp [ht]
    simp [hst, ht_real]
  ·
    have ht_real : (margY t).toReal ≠ 0 := by
      intro h
      rw [ENNReal.toReal_eq_zero_iff] at h
      exact ht (h.elim id (absurd · (PMF.apply_ne_top margY t)))
    have hst_sum : ∑ s : S, (p (s, t)).toReal = (margY t).toReal :=
      sum_toReal_eq_margY_toReal p t
    have hst_div_sum : ∑ s : S, (p (s, t)).toReal / (margY t).toReal = 1 := by
      rw [← Finset.sum_div, hst_sum, div_self ht_real]
    have key : ∀ s, negMulLog (p (s, t)).toReal =
      (margY t).toReal * negMulLog ((p (s, t)).toReal / (margY t).toReal) +
      ((p (s, t)).toReal / (margY t).toReal) * negMulLog (margY t).toReal := by
      intro s
      have heq : (p (s, t)).toReal =
        ((p (s, t)).toReal / (margY t).toReal) * (margY t).toReal := by
        field_simp
      conv_lhs => rw [heq]
      rw [negMulLog_mul]
    simp_rw [key, Finset.sum_add_distrib, ← Finset.sum_mul, hst_div_sum, one_mul,
      ← Finset.mul_sum, add_comm]

end ShannonEntropy

namespace ShannonEntropy

/--
[conditionalEntropy_le_shannonEntropy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma conditionalEntropy_le_shannonEntropy
  [Fintype S]
  [Fintype T]
  [DecidableEq S]
  [DecidableEq T]
  {p : PMF (S × T)} :
-- imply
  conditionalEntropy p ≤ shannonEntropy (PMF.map Prod.fst p) := by
-- proof
  show (∑ t : T, ((PMF.map Prod.snd p) t).toReal *
    ∑ s : S, negMulLog ((p (s, t)).toReal / ((PMF.map Prod.snd p) t).toReal)) ≤
    ∑ s : S, negMulLog ((PMF.map Prod.fst p s).toReal)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s _
  have hw_nn : ∀ i ∈ (univ : Finset T), 0 ≤ ((PMF.map Prod.snd p) i).toReal :=
    fun _ _ => ENNReal.toReal_nonneg
  have hw_sum : ∑ i ∈ (univ : Finset T), ((PMF.map Prod.snd p) i).toReal = 1 :=
    pmf_sum_toReal_eq_one (PMF.map Prod.snd p)
  have hc_nn : ∀ i ∈ (univ : Finset T),
    (p (s, i)).toReal / ((PMF.map Prod.snd p) i).toReal ∈ Set.Ici (0 : ℝ) :=
    fun _ _ => Set.mem_Ici.mpr (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have jensen := concaveOn_negMulLog.le_map_sum hw_nn hw_sum hc_nn
  simp only [smul_eq_mul] at jensen
  rwa [total_prob_toReal] at jensen

end ShannonEntropy

namespace ShannonEntropy

/--
[margYZ_sum_eq_margZ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma margYZ_sum_eq_margZ
  [Fintype S]
  [Fintype T]
  [Fintype U]
  [DecidableEq S]
  [DecidableEq T]
  [DecidableEq U]
  {p : PMF (S × (T × U))}
  {u : U} :
-- imply
  ∑ t : T, (PMF.map Prod.snd p) (t, u) = (PMF.map Prod.snd (PMF.map (fun x : S × (T × U) => (x.1, x.2.2)) p)) u := by
-- proof
  have hlhs : ∑ t : T, (PMF.map Prod.snd p) (t, u) =
    (PMF.map Prod.snd (PMF.map Prod.snd p)) u := by
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    simp_rw [eq_comm (a := u), Fintype.sum_ite_eq' u]
  have hrhs : (PMF.map Prod.snd (PMF.map (fun x : S × (T × U) => (x.1, x.2.2)) p)) u =
    (PMF.map Prod.snd (PMF.map Prod.snd p)) u := by
    congr 1; rw [PMF.map_comp, PMF.map_comp]; congr 1
  rw [hlhs, hrhs]

end ShannonEntropy

namespace ShannonEntropy

/--
[pmf_proj_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma pmf_proj_apply
  [Fintype S]
  [Fintype T]
  [Fintype U]
  [DecidableEq S]
  [DecidableEq U]
  {p : PMF (S × (T × U))}
  {s : S}
  {u : U} :
-- imply
  (PMF.map (fun x : S × (T × U) => (x.1, x.2.2)) p) (s, u) = ∑ t : T, p (s, (t, u)) := by
-- proof
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Prod.mk.injEq]
  have h1 : ∀ x : S, ∀ t : T,
    (∑ x_2 : U, if s = x ∧ u = x_2 then p (x, (t, x_2)) else 0) =
    if s = x then p (x, (t, u)) else 0 := by
    intro x t
    by_cases hx : s = x
    · subst hx; simp only [true_and, ite_true, eq_comm (a := u)]
      exact Fintype.sum_ite_eq' u (fun v => p (s, (t, v)))
    · simp [hx]
  simp_rw [h1, eq_comm (a := s)]
  simp [Fintype.sum_ite_eq' s]

end ShannonEntropy

namespace ShannonEntropy

/--
[conditionalEntropy_drop_conditioning](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma conditionalEntropy_drop_conditioning
  [Fintype S]
  [Fintype T]
  [Fintype U]
  [DecidableEq S]
  [DecidableEq T]
  [DecidableEq U]
  {p : PMF (S × (T × U))} :
-- imply
  conditionalEntropy p ≤ conditionalEntropy (PMF.map (fun x : S × (T × U) => (x.1, x.2.2)) p) := by
-- proof
  set q := PMF.map (fun x : S × (T × U) => (x.1, x.2.2)) p with hq_def
  set margYZ := PMF.map Prod.snd p with hmargYZ_def
  set margZ := PMF.map Prod.snd q with hmargZ_def
  show (∑ tu : T × U, (margYZ tu).toReal *
    ∑ s, negMulLog ((p (s, tu)).toReal / (margYZ tu).toReal)) ≤
    (∑ u : U, (margZ u).toReal *
    ∑ s, negMulLog ((q (s, u)).toReal / (margZ u).toReal))
  rw [Fintype.sum_prod_type, Finset.sum_comm (s := univ) (t := univ)]
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : margZ u = 0
  ·
    have hmarg_sum : ∑ t : T, margYZ (t, u) = 0 := by
      rw [margYZ_sum_eq_margZ]; exact hu
    have hterms : ∀ t : T, margYZ (t, u) = 0 := by
      intro t
      exact le_antisymm
        ((Finset.single_le_sum (f := fun t' => margYZ (t', u)) (fun _ _ => zero_le _)
          (mem_univ t)).trans (le_of_eq hmarg_sum)) (zero_le _)
    have lhs_zero : (∑ t : T, (margYZ (t, u)).toReal *
      ∑ s, negMulLog ((p (s, (t, u))).toReal / (margYZ (t, u)).toReal)) = 0 := by
      apply Finset.sum_eq_zero; intro t _; simp [hterms t]
    rw [lhs_zero, hu]; simp
  ·
    have hmZ_pos : (0 : ℝ) < (margZ u).toReal :=
      ENNReal.toReal_pos hu (PMF.apply_ne_top _ _)
    calc ∑ t : T, (margYZ (t, u)).toReal *
      ∑ s, negMulLog ((p (s, (t, u))).toReal / (margYZ (t, u)).toReal)
      = ∑ s : S, ∑ t : T, (margYZ (t, u)).toReal *
        negMulLog ((p (s, (t, u))).toReal / (margYZ (t, u)).toReal) := by
        simp_rw [Finset.mul_sum]; exact Finset.sum_comm
      _ ≤ ∑ s : S, (margZ u).toReal *
        negMulLog ((q (s, u)).toReal / (margZ u).toReal) := by
        apply Finset.sum_le_sum; intro s _
        have hfactor : ∀ t : T, (margYZ (t, u)).toReal *
          negMulLog ((p (s, (t, u))).toReal / (margYZ (t, u)).toReal) =
          (margZ u).toReal * ((margYZ (t, u)).toReal / (margZ u).toReal *
            negMulLog ((p (s, (t, u))).toReal / (margYZ (t, u)).toReal)) := by
          intro t
          have hne := ne_of_gt hmZ_pos
          field_simp
        simp_rw [hfactor, ← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hmZ_pos)
        have hw_nn : ∀ t ∈ (univ : Finset T),
          0 ≤ (margYZ (t, u)).toReal / (margZ u).toReal :=
          fun _ _ => div_nonneg ENNReal.toReal_nonneg (le_of_lt hmZ_pos)
        have hw_sum : ∑ t ∈ (univ : Finset T),
          (margYZ (t, u)).toReal / (margZ u).toReal = 1 := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul, mul_inv_eq_one₀ (ne_of_gt hmZ_pos)]
          rw [← ENNReal.toReal_sum (fun t _ => PMF.apply_ne_top margYZ (t, u))]
          congr 1; exact margYZ_sum_eq_margZ p u
        have hvals : ∀ t ∈ (univ : Finset T),
          (p (s, (t, u))).toReal / (margYZ (t, u)).toReal ∈ Set.Ici (0 : ℝ) :=
          fun _ _ => Set.mem_Ici.mpr (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        have jensen := concaveOn_negMulLog.le_map_sum hw_nn hw_sum hvals
        simp only [smul_eq_mul] at jensen
        have htotal : ∑ t ∈ (univ : Finset T),
          (margYZ (t, u)).toReal / (margZ u).toReal *
          ((p (s, (t, u))).toReal / (margYZ (t, u)).toReal) =
          (q (s, u)).toReal / (margZ u).toReal := by
          have hterm : ∀ t : T,
            (margYZ (t, u)).toReal / (margZ u).toReal *
              ((p (s, (t, u))).toReal / (margYZ (t, u)).toReal) =
            (p (s, (t, u))).toReal / (margZ u).toReal := by
            intro t
            by_cases ht : margYZ (t, u) = 0
            · have hst : p (s, (t, u)) = 0 :=
              le_antisymm ((pmf_le_map_snd p s (t, u)).trans (le_of_eq ht)) (zero_le _)
              simp [ht, hst]
            · rw [div_mul_div_comm, mul_comm, mul_div_mul_right _ _
              (ENNReal.toReal_ne_zero.mpr ⟨ht, PMF.apply_ne_top _ _⟩)]
          simp_rw [hterm, div_eq_mul_inv, ← Finset.sum_mul]
          congr 1
          rw [pmf_proj_apply, ENNReal.toReal_sum
            (fun t _ => PMF.apply_ne_top p (s, (t, u)))]
        rwa [htotal] at jensen
      _ = (margZ u).toReal *
        ∑ s, negMulLog ((q (s, u)).toReal / (margZ u).toReal) := by
        rw [Finset.mul_sum]

end ShannonEntropy

namespace ShannonEntropy

/--
[entropy_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma entropy_subadditive
  [Fintype S]
  [Fintype T]
  [DecidableEq S]
  [DecidableEq T]
  {p : PMF (S × T)} :
-- imply
  shannonEntropy p ≤ shannonEntropy (PMF.map Prod.fst p) + shannonEntropy (PMF.map Prod.snd p) := by
-- proof
  rw [entropy_chain_rule]
  linarith [conditionalEntropy_le_shannonEntropy p]

end ShannonEntropy

namespace ShannonEntropy

/--
[shannonEntropy_map_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma shannonEntropy_map_equiv
  [Fintype S]
  [Fintype T]
  [DecidableEq S]
  [DecidableEq T]
  {p : PMF S}
  {e : S ≃ T} :
-- imply
  shannonEntropy (PMF.map e p) = shannonEntropy p := by
-- proof
  simp only [shannonEntropy]
  rw [← e.sum_comp (fun t => negMulLog ((PMF.map e p) t).toReal)]
  congr 1; ext s; congr 1; congr 1
  simp [PMF.map_apply, tsum_fintype, e.injective.eq_iff]

end ShannonEntropy

namespace ShannonEntropy

/--
[marginal_succFunEquiv_snd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma marginal_succFunEquiv_snd
  {n : ℕ}
  [Fintype α]
  [DecidableEq α]
  {p : PMF (Fin (n + 1) → α)} :
-- imply
  PMF.map Prod.snd (PMF.map (Fin.succFunEquiv α n) p) = marginal p (Fin.last n) := by
-- proof
  simp only [marginal]; rw [PMF.map_comp]; congr 1

end ShannonEntropy

namespace ShannonEntropy

/--
[marginal_succFunEquiv_fst](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma marginal_succFunEquiv_fst
  {n : ℕ}
  [Fintype α]
  [DecidableEq α]
  {p : PMF (Fin (n + 1) → α)}
  {i : Fin n} :
-- imply
  marginal (PMF.map Prod.fst (PMF.map (Fin.succFunEquiv α n) p)) i = marginal p (i.castSucc) := by
-- proof
  simp only [marginal]; rw [PMF.map_comp, PMF.map_comp]; congr 1
set_option maxHeartbeats 400000 in

end ShannonEntropy

namespace ShannonEntropy

/--
[entropy_subadditive_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean)
-/
@[path]
lemma entropy_subadditive_general
  {n : ℕ}
  [Fintype α]
  [DecidableEq α]
  {p : PMF (Fin n → α)} :
-- imply
  shannonEntropy p ≤ ∑ i : Fin n, shannonEntropy (marginal p i) := by
-- proof
  induction n with
  | zero =>
    have : Unique (Fin 0 → α) := Pi.uniqueOfIsEmpty _
    have huniv : (univ : Finset (Fin 0 → α)) = {default} := Finset.univ_unique
    simp only [shannonEntropy, huniv, Finset.sum_singleton]
    have hp : p default = 1 := by
      have := PMF.tsum_coe p
      rw [tsum_fintype, huniv, Finset.sum_singleton] at this
      exact_mod_cast this
    simp [hp, negMulLog_one]
  | succ n ih =>
    set q := PMF.map (Fin.succFunEquiv α n) p
    have h1 : shannonEntropy p = shannonEntropy q := by
      rw [shannonEntropy_map_equiv]
    have h2 : shannonEntropy q ≤
      shannonEntropy (PMF.map Prod.fst q) + shannonEntropy (PMF.map Prod.snd q) :=
      entropy_subadditive q
    have h3 : shannonEntropy (PMF.map Prod.fst q) ≤
      ∑ i : Fin n, shannonEntropy (marginal (PMF.map Prod.fst q) i) :=
      ih (PMF.map Prod.fst q)
    have h4 : ∀ i : Fin n, shannonEntropy (marginal (PMF.map Prod.fst q) i) =
      shannonEntropy (marginal p i.castSucc) := by
      intro i; rw [marginal_succFunEquiv_fst]
    have h5 : shannonEntropy (PMF.map Prod.snd q) =
      shannonEntropy (marginal p (Fin.last n)) := by
      congr 1; exact marginal_succFunEquiv_snd p
    rw [Fin.sum_univ_castSucc]
    calc shannonEntropy p = shannonEntropy q := h1
      _ ≤ shannonEntropy (PMF.map Prod.fst q) + shannonEntropy (PMF.map Prod.snd q) := h2
      _ ≤ (∑ i : Fin n, shannonEntropy (marginal (PMF.map Prod.fst q) i)) +
        shannonEntropy (PMF.map Prod.snd q) := by linarith [h3]
      _ = (∑ i : Fin n, shannonEntropy (marginal p i.castSucc)) +
        shannonEntropy (marginal p (Fin.last n)) := by
        rw [h5]; congr 1; exact Finset.sum_congr rfl (fun i _ => h4 i)

end ShannonEntropy


-- created on 2026-10-23
