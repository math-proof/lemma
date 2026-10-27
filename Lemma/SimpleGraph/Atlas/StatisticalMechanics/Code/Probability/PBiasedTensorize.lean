import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part11
open Finset Real StatMech StatMech.Probability


/--
[ptn_val_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_val_true_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ptn_val true = 1 := by
-- proof
  apply StatMech.Probability.ptn_val_true

/--
[ptn_val_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_val_false_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ptn_val false = 0 := by
-- proof
  apply StatMech.Probability.ptn_val_false

/--
[ptn_sigma_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_sigma_pos_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < ptn_sigma p := by
-- proof
  apply StatMech.Probability.ptn_sigma_pos hp0 hp1

/--
[ptn_sigma_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_sigma_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ptn_sigma p ^ 2 = p * (1 - p) := by
-- proof
  apply StatMech.Probability.ptn_sigma_sq hp0 hp1

/--
[ptn_psi_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_psi_mean_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (1 - p) * ptn_psi p false + p * ptn_psi p true = 0 := by
-- proof
  apply StatMech.Probability.ptn_psi_mean hp0 hp1

/--
[ptn_psi_sq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_psi_sq_mean_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (1 - p) * ptn_psi p false ^ 2 + p * ptn_psi p true ^ 2 = 1 := by
-- proof
  apply StatMech.Probability.ptn_psi_sq_mean hp0 hp1

/--
[ptn_expect_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_expect_prod_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (h : ι → Bool → ℝ) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ∏ e : ι, h e (ω e)) = ∏ e : ι, ((1 - p) * h e false + p * h e true) := by
-- proof
  apply StatMech.Probability.ptn_expect_prod p h

/--
[ptn_pchar_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_pchar_empty_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {ω : ConfigSpace ι} :
-- imply
  ptn_pchar p (∅ : Finset ι) ω = 1 := by
-- proof
  apply StatMech.Probability.ptn_pchar_empty p ω

/--
[ptn_pchar_as_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_pchar_as_univ_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {S : Finset ι}
  {ω : ConfigSpace ι} :
-- imply
  ptn_pchar p S ω = ∏ i : ι, (if i ∈ S then ptn_psi p (ω i) else 1) := by
-- proof
  apply StatMech.Probability.ptn_pchar_as_univ p S ω

/--
[ptn_orthonormal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_orthonormal_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {S T : Finset ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ptn_pchar p S ω * ptn_pchar p T ω) = if S = T then 1 else 0 := by
-- proof
  apply StatMech.Probability.ptn_orthonormal hp0 hp1 S T

/--
[ptn_coeff_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_coeff_empty_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {f : ConfigSpace ι → ℝ} :
-- imply
  ptn_coeff p f ∅ = OSSS.expect (OSSS.bernoulliWeight p) f := by
-- proof
  apply StatMech.Probability.ptn_coeff_empty p f

/--
[ptn_repro_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_repro_kernel_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {x y : ConfigSpace ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ S : Finset ι, ptn_pchar p S x * ptn_pchar p S y) = if x = y then 1 / OSSS.weight (OSSS.bernoulliWeight p) x else 0 := by
-- proof
  apply StatMech.Probability.ptn_repro_kernel hp0 hp1 x y

/--
[ptn_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_expansion_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {f : ConfigSpace ι → ℝ}
  {x : ConfigSpace ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S x) = f x := by
-- proof
  apply StatMech.Probability.ptn_expansion hp0 hp1 f x

/--
[ptn_expect_finsetSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_expect_finsetSum_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {s : Finset κ}
  {g : κ → ConfigSpace ι → ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ∑ k ∈ s, g k ω) = ∑ k ∈ s, OSSS.expect (OSSS.bernoulliWeight p) (g k) := by
-- proof
  apply StatMech.Probability.ptn_expect_finsetSum p s g

/--
[ptn_parseval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_parseval_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {f g : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => f ω * g ω) = ∑ S : Finset ι, ptn_coeff p f S * ptn_coeff p g S := by
-- proof
  apply StatMech.Probability.ptn_parseval hp0 hp1 f g

/--
[ptn_parseval_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_parseval_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2) = ∑ S : Finset ι, (ptn_coeff p f S) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_parseval_sq hp0 hp1 f

/--
[ptn_var_eq_fourierWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_var_eq_fourierWeight_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) f = ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_var_eq_fourierWeight hp0 hp1 f

/--
[ptn_psi_jump](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_psi_jump_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (_hp0 : 0 < p)
  (_hp1 : p < 1) :
-- imply
  ptn_psi p true - ptn_psi p false = 1 / ptn_sigma p := by
-- proof
  apply StatMech.Probability.ptn_psi_jump _hp0 _hp1

/--
[ptn_pchar_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_pchar_deriv_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {S : Finset ι}
  {e : ι}
  {ω : ConfigSpace ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ptn_pchar p S (StatMech.setOpen e ω) - ptn_pchar p S (StatMech.setClosed e ω) = if e ∈ S then (1 / ptn_sigma p) * ptn_pchar p (S.erase e) ω else 0 := by
-- proof
  apply StatMech.Probability.ptn_pchar_deriv hp0 hp1 S e ω

/--
[ptn_deriv_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_deriv_fourier_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {f : ConfigSpace ι → ℝ}
  {e : ι}
  {ω : ConfigSpace ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  f (StatMech.setOpen e ω) - f (StatMech.setClosed e ω) = ∑ S ∈ univ.filter (fun S => e ∈ S), (ptn_coeff p f S / ptn_sigma p) * ptn_pchar p (S.erase e) ω := by
-- proof
  apply StatMech.Probability.ptn_deriv_fourier hp0 hp1 f e ω

/--
[ptn_expect_sum_pchar_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_expect_sum_pchar_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {s : Finset (Finset ι)}
  {a : Finset ι → ℝ}
  {T : Finset ι → Finset ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hTinj : Set.InjOn T s) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (∑ S ∈ s, a S * ptn_pchar p (T S) ω) ^ 2) = ∑ S ∈ s, (a S) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_expect_sum_pchar_sq hp0 hp1 s a T hTinj

/--
[ptn_erase_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_erase_injOn_eq
  [Fintype ι]
  [DecidableEq ι]
  {e : ι} :
-- imply
  Set.InjOn (fun S => Finset.erase S e) ↑(univ.filter (fun S : Finset ι => e ∈ S)) := by
-- proof
  apply StatMech.Probability.ptn_erase_injOn e

/--
[ptn_abs_diff_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_abs_diff_indicator_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {e : ι}
  {ω : ConfigSpace ι} :
-- imply
  |(fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω) - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)| = ((fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω) - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_abs_diff_indicator φ e ω

/--
[ptn_infl_eq_fourierWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_infl_eq_fourierWeight_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e = (1 / (ptn_sigma p) ^ 2) * ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_infl_eq_fourierWeight hp0 hp1 φ e

/--
[ptn_totalInfl_eq_fourierWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_totalInfl_eq_fourierWeight_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_totalInfl_eq_fourierWeight hp0 hp1 φ

/--
[ptn_qnormPow_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_qnormPow_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {q : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ ptn_qnormPow p q f := by
-- proof
  apply StatMech.Probability.ptn_qnormPow_nonneg hp0 hp1 q f

/--
[ptn_qnorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_qnorm_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {q : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ ptn_qnorm p q f := by
-- proof
  apply StatMech.Probability.ptn_qnorm_nonneg hp0 hp1 q f

/--
[ptn_qnorm_rpow_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_qnorm_rpow_self_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {q : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq : q ≠ 0) :
-- imply
  ptn_qnorm p q f ^ q = ptn_qnormPow p q f := by
-- proof
  apply StatMech.Probability.ptn_qnorm_rpow_self hp0 hp1 hq f

/--
[ptn_noiseOp_l2sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_noiseOp_l2sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {ρ : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (ptn_noiseOp p ρ f ω) ^ 2) = ∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_noiseOp_l2sq hp0 hp1 ρ f

/--
[ptn_qnormPow2_eq_expect_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_qnormPow2_eq_expect_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {f : ConfigSpace ι → ℝ} :
-- imply
  ptn_qnormPow p 2 f = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2) := by
-- proof
  apply StatMech.Probability.ptn_qnormPow2_eq_expect_sq f

/--
[ptn_qnorm2_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_qnorm2_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  (ptn_qnorm p 2 f) ^ 2 = ptn_qnormPow p 2 f := by
-- proof
  apply StatMech.Probability.ptn_qnorm2_sq hp0 hp1 f

/--
[ptn_sum_cons_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_sum_cons_split_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  [AddCommMonoid M]
  {F : (Fin (n + 1) → Bool) → M} :
-- imply
  (∑ y : Fin (n + 1) → Bool, F y) = ∑ c : Bool, ∑ ω' : Fin n → Bool, F (Fin.cons c ω') := by
-- proof
  apply StatMech.Probability.ptn_sum_cons_split F

/--
[ptn_expect_cons_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_expect_cons_split_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {p : ℝ}
  {f : (Fin (n + 1) → Bool) → ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) f = (1 - p) * OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => f (Fin.cons false ω')) + p * OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => f (Fin.cons true ω')) := by
-- proof
  apply StatMech.Probability.ptn_expect_cons_split p f

/--
[ptn_kop_pchar_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kop_pchar_apply_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {ρ : ℝ}
  {S : Finset ι}
  {x : ConfigSpace ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ptn_kop p ρ (ptn_pchar p S) x = ρ ^ S.card * ptn_pchar p S x := by
-- proof
  apply StatMech.Probability.ptn_kop_pchar_apply hp0 hp1 ρ S x

/--
[ptn_kop_finsetSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kop_finsetSum_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ : ℝ}
  {s : Finset κ}
  {g : κ → ConfigSpace ι → ℝ} :
-- imply
  ptn_kop p ρ (fun x => ∑ k ∈ s, g k x) = fun x => ∑ k ∈ s, ptn_kop p ρ (g k) x := by
-- proof
  apply StatMech.Probability.ptn_kop_finsetSum p ρ s g

/--
[ptn_kop_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kop_const_mul_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ c : ℝ}
  {g : ConfigSpace ι → ℝ} :
-- imply
  ptn_kop p ρ (fun x => c * g x) = fun x => c * ptn_kop p ρ g x := by
-- proof
  apply StatMech.Probability.ptn_kop_const_mul p ρ c g

/--
[ptn_kop_eq_noiseOp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kop_eq_noiseOp_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {ρ : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ptn_kop p ρ f = ptn_noiseOp p ρ f := by
-- proof
  apply StatMech.Probability.ptn_kop_eq_noiseOp hp0 hp1 ρ f

/--
[ptn_expect_sq_lincomb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_expect_sq_lincomb_eq
  [Fintype ι]
  [DecidableEq ι]
  {p a b : ℝ}
  {u v : ConfigSpace ι → ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (a * u ω + b * v ω) ^ 2) = a ^ 2 * OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (u ω) ^ 2) + 2 * a * b * OSSS.expect (OSSS.bernoulliWeight p) (fun ω => u ω * v ω) + b ^ 2 * OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (v ω) ^ 2) := by
-- proof
  apply StatMech.Probability.ptn_expect_sq_lincomb p a b u v

/--
[ptn_expect_inner_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_expect_inner_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {u v : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => u ω * v ω) ≤ Real.sqrt (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (u ω) ^ 2)) * Real.sqrt (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (v ω) ^ 2)) := by
-- proof
  apply StatMech.Probability.ptn_expect_inner_le hp0 hp1 u v

/--
[ptn_kernel_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kernel_cons_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {p ρ : ℝ}
  {a c : Bool}
  {ω ω' : Fin n → Bool} :
-- imply
  ptn_kernel p ρ (Fin.cons a ω) (Fin.cons c ω') = ptn_kbit p ρ a c * ptn_kernel p ρ ω ω' := by
-- proof
  apply StatMech.Probability.ptn_kernel_cons p ρ a c ω ω'

/--
[ptn_kop_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kop_cons_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {p ρ : ℝ}
  {f : (Fin (n + 1) → Bool) → ℝ}
  {a : Bool}
  {ω : Fin n → Bool} :
-- imply
  ptn_kop p ρ f (Fin.cons a ω) = ∑ c : Bool, ptn_kbit p ρ a c * ptn_kop p ρ (fun ω' : Fin n → Bool => f (Fin.cons c ω')) ω := by
-- proof
  apply StatMech.Probability.ptn_kop_cons p ρ f a ω

/--
[ptn_kop_cons_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kop_cons_pair_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {p ρ : ℝ}
  {f : (Fin (n + 1) → Bool) → ℝ}
  {a : Bool}
  {ω : Fin n → Bool} :
-- imply
  ptn_kop p ρ f (Fin.cons a ω) = ptn_kbit p ρ a false * ptn_kop p ρ (fun ω' => f (Fin.cons false ω')) ω + ptn_kbit p ρ a true * ptn_kop p ρ (fun ω' => f (Fin.cons true ω')) ω := by
-- proof
  apply StatMech.Probability.ptn_kop_cons_pair p ρ f a ω

/--
[ptn_kop_fin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kop_fin_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ : ℝ}
  {f : (Fin 0 → Bool) → ℝ} :
-- imply
  ptn_kop p ρ f = f := by
-- proof
  apply StatMech.Probability.ptn_kop_fin_zero p ρ f

/--
[ptn_qnorm_fin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_qnorm_fin_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  {p q : ℝ}
  {f : (Fin 0 → Bool) → ℝ}
-- given
  (hq : 0 < q) :
-- imply
  ptn_qnorm p q f = |f default| := by
-- proof
  apply StatMech.Probability.ptn_qnorm_fin_zero hq f

/--
[ptn_qnormPow_cons_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_qnormPow_cons_split_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {p q : ℝ}
  {f : (Fin (n + 1) → Bool) → ℝ} :
-- imply
  ptn_qnormPow p q f = (1 - p) * ptn_qnormPow p q (fun ω' : Fin n → Bool => f (Fin.cons false ω')) + p * ptn_qnormPow p q (fun ω' : Fin n → Bool => f (Fin.cons true ω')) := by
-- proof
  apply StatMech.Probability.ptn_qnormPow_cons_split p q f

/--
[ptn_kbit_ff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kbit_ff_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ : ℝ} :
-- imply
  ptn_kbit p ρ false false = ρ + (1 - ρ) * (1 - p) := by
-- proof
  apply StatMech.Probability.ptn_kbit_ff p ρ

/--
[ptn_kbit_ft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kbit_ft_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ : ℝ} :
-- imply
  ptn_kbit p ρ false true = (1 - ρ) * p := by
-- proof
  apply StatMech.Probability.ptn_kbit_ft p ρ

/--
[ptn_kbit_tf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kbit_tf_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ : ℝ} :
-- imply
  ptn_kbit p ρ true false = (1 - ρ) * (1 - p) := by
-- proof
  apply StatMech.Probability.ptn_kbit_tf p ρ

/--
[ptn_kbit_tt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kbit_tt_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ : ℝ} :
-- imply
  ptn_kbit p ρ true true = ρ + (1 - ρ) * p := by
-- proof
  apply StatMech.Probability.ptn_kbit_tt p ρ

/--
[ptn_kop_l2sq_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kop_l2sq_cons_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {p ρ : ℝ}
  {f : (Fin (n + 1) → Bool) → ℝ} :
-- imply
  ptn_qnormPow p 2 (ptn_kop p ρ f) = (1 - p) * OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => (ptn_kbit p ρ false false * ptn_kop p ρ (fun ω' => f (Fin.cons false ω')) ω + ptn_kbit p ρ false true * ptn_kop p ρ (fun ω' => f (Fin.cons true ω')) ω) ^ 2) + p * OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => (ptn_kbit p ρ true false * ptn_kop p ρ (fun ω' => f (Fin.cons false ω')) ω + ptn_kbit p ρ true true * ptn_kop p ρ (fun ω' => f (Fin.cons true ω')) ω) ^ 2) := by
-- proof
  apply StatMech.Probability.ptn_kop_l2sq_cons p ρ f

/--
[ptn_cons_quadform_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_cons_quadform_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p q ρ u v : ℝ}
-- given
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  (1 - p) * (ptn_kbit p ρ false false * u + ptn_kbit p ρ false true * v) ^ 2 + p * (ptn_kbit p ρ true false * u + ptn_kbit p ρ true true * v) ^ 2 = ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_cons_quadform_eq hρsq

/--
[ptn_kbit_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kbit_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ : ℝ}
  {a c : Bool}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ ptn_kbit p ρ a c := by
-- proof
  apply StatMech.Probability.ptn_kbit_nonneg h0 h1 hp0 hp1 a c

/--
[ptn_tensorStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_tensorStep_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
  (ih : ∀ g : (Fin n → Bool) → ℝ, ptn_qnorm p 2 (ptn_kop p ρ g) ≤ ptn_qnorm p q g) :
-- imply
  ptn_qnorm p 2 (ptn_kop p ρ f) ≤ ptn_qnorm p q f := by
-- proof
  apply StatMech.Probability.ptn_tensorStep hp0 hp1 h0 h1 hq1 hq2 hρsq n ih f

/--
[ptn_hypercontractivity_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_hypercontractivity_fin_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  ptn_qnorm p 2 (ptn_kop p ρ f) ≤ ptn_qnorm p q f := by
-- proof
  apply StatMech.Probability.ptn_hypercontractivity_fin hp0 hp1 h0 h1 hq1 hq2 hρsq n f

/--
[ptn_lowDegreeWeight_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_lowDegreeWeight_fin_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  (∑ S : Finset (Fin n), (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2) ≤ (ptn_qnorm p q f) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_lowDegreeWeight_fin hp0 hp1 h0 h1 hq1 hq2 hρsq n f

/--
[ptn_expect_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_expect_reindex_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {σ : κ ≃ ι}
  {p : ℝ}
  {f : ConfigSpace ι → ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (ptn_reindex σ f) = OSSS.expect (OSSS.bernoulliWeight p) f := by
-- proof
  apply StatMech.Probability.ptn_expect_reindex σ p f

/--
[ptn_qnorm_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_qnorm_reindex_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {σ : κ ≃ ι}
  {p q : ℝ}
  {f : ConfigSpace ι → ℝ} :
-- imply
  ptn_qnorm p q (ptn_reindex σ f) = ptn_qnorm p q f := by
-- proof
  apply StatMech.Probability.ptn_qnorm_reindex σ p q f

/--
[ptn_kop_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kop_reindex_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {σ : κ ≃ ι}
  {p ρ : ℝ}
  {f : ConfigSpace ι → ℝ} :
-- imply
  ptn_kop p ρ (ptn_reindex σ f) = ptn_reindex σ (ptn_kop p ρ f) := by
-- proof
  apply StatMech.Probability.ptn_kop_reindex σ p ρ f

/--
[ptn_lowDegreeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_lowDegreeWeight_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {f : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2) ≤ (ptn_qnorm p q f) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_lowDegreeWeight hp0 hp1 h0 h1 hq1 hq2 hρsq f

/--
[ptn_qnormPow_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_qnormPow_deriv_eq
  [Fintype ι]
  [DecidableEq ι]
  {p q : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hq : 0 < q) :
-- imply
  ptn_qnormPow p q (ptn_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e) = OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
-- proof
  apply StatMech.Probability.ptn_qnormPow_deriv hq φ e

/--
[ptn_qnorm_deriv_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_qnorm_deriv_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p q : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (ptn_qnorm p q (ptn_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e)) ^ 2 = (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.ptn_qnorm_deriv_sq hp0 hp1 hq φ e

/--
[ptn_kop_deriv_l2sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kop_deriv_l2sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {ρ : ℝ}
  {f : ConfigSpace ι → ℝ}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun x => (ptn_kop p ρ (ptn_deriv f e) x) ^ 2) = ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p f S / ptn_sigma p) ^ 2 := by
-- proof
  apply StatMech.Probability.ptn_kop_deriv_l2sq hp0 hp1 ρ f e

/--
[ptn_perCoord_hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_perCoord_hc_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma p) ^ 2) ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.ptn_perCoord_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ e

/--
[ptn_summed_hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_summed_hc_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.ptn_summed_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ

/--
[ptn_cap_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_cap_sum_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  (∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q)) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.ptn_cap_sum hp0 hp1 hq1 hq2 φ

/--
[ptn_capped_hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_capped_hc_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.ptn_capped_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ

/--
[ptn_rhoOptimise_hyp_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_rhoOptimise_hyp_holds_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ q' : ℝ, 1 ≤ q' → q' ≤ 2 → ρ ^ 2 = (q' - 1) * 4 * p * (1 - p) → (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.ptn_rhoOptimise_hyp_holds hp0 hp1 φ

/--
[ptn_kklHC_of_rhoOptimise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_kklHC_of_rhoOptimise_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : ptn_RhoOptimise q}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  KKLHypercontractive p 2 := by
-- proof
  apply StatMech.Probability.ptn_kklHC_of_rhoOptimise H hp hp1

/--
[ptn_PBiasedHC_of_rhoOptimise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_PBiasedHC_of_rhoOptimise_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : ptn_RhoOptimise q}
-- given
  (hq : q ≤ 1) :
-- imply
  kpb_PBiasedHC q := by
-- proof
  apply StatMech.Probability.ptn_PBiasedHC_of_rhoOptimise hq H

/--
[ptn_rhoOptimise_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_rhoOptimise_c0_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  (0 : ℝ) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.ptn_rhoOptimise_c0 hp0 hp1 φ

/--
[ptn_residue_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_residue_noncirc_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : ptn_RhoOptimise q}
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.ptn_residue_noncirc H hp hp1 φ

/--
[ptn_sharpThreshold_of_rhoOptimise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean)
-/
@[path]
private lemma ptn_sharpThreshold_of_rhoOptimise_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : ptn_RhoOptimise q}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {v₀ L : ℝ}
-- given
  (hq1 : q ≤ 1)
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
  (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
-- imply
  1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A := by
-- proof
  apply StatMech.Probability.ptn_sharpThreshold_of_rhoOptimise hq1 H A hA hq hv0 hL hhalf hvar hLL'


-- created on 2026-10-23
