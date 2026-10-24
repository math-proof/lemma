import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.KKLfromHC
open Finset StatMech StatMech.Probability


/--
[khc_sign_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_sign_false_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  khc_sign false = 1 := by
-- proof
  apply StatMech.Probability.khc_sign_false

/--
[khc_sign_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_sign_true_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  khc_sign true = -1 := by
-- proof
  apply StatMech.Probability.khc_sign_true

/--
[khc_sign_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_sign_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {b : Bool} :
-- imply
  khc_sign b * khc_sign b = 1 := by
-- proof
  apply StatMech.Probability.khc_sign_sq b

/--
[khc_walshChar_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_walshChar_empty_eq
  [Fintype ι]
  [DecidableEq ι]
  {x : ι → Bool} :
-- imply
  khc_walshChar (∅ : Finset ι) x = 1 := by
-- proof
  apply StatMech.Probability.khc_walshChar_empty x

/--
[khc_walshChar_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_walshChar_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {S : Finset ι}
  {x : ι → Bool} :
-- imply
  (khc_walshChar S x) ^ 2 = 1 := by
-- proof
  apply StatMech.Probability.khc_walshChar_sq S x

/--
[khc_walshChar_as_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_walshChar_as_univ_eq
  [Fintype ι]
  [DecidableEq ι]
  {S : Finset ι}
  {x : ι → Bool} :
-- imply
  khc_walshChar S x = ∏ i : ι, (if i ∈ S then khc_sign (x i) else 1) := by
-- proof
  apply StatMech.Probability.khc_walshChar_as_univ S x

/--
[khc_walshChar_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_walshChar_mul_eq
  [Fintype ι]
  [DecidableEq ι]
  {S T : Finset ι}
  {x : ι → Bool} :
-- imply
  khc_walshChar S x * khc_walshChar T x = khc_walshChar (symmDiff S T) x := by
-- proof
  apply StatMech.Probability.khc_walshChar_mul S T x

/--
[khc_uexp_walshChar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_uexp_walshChar_eq
  [Fintype ι]
  [DecidableEq ι]
  {S : Finset ι} :
-- imply
  bnt_uexp (khc_walshChar S) = if S = ∅ then 1 else 0 := by
-- proof
  apply StatMech.Probability.khc_uexp_walshChar S

/--
[khc_orthonormal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_orthonormal_eq
  [Fintype ι]
  [DecidableEq ι]
  {S T : Finset ι} :
-- imply
  bnt_uexp (fun x => khc_walshChar S x * khc_walshChar T x) = if S = T then 1 else 0 := by
-- proof
  apply StatMech.Probability.khc_orthonormal S T

/--
[khc_sum_walshChar_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_sum_walshChar_mul_eq
  [Fintype ι]
  [DecidableEq ι]
  {x y : ι → Bool} :
-- imply
  (∑ S : Finset ι, khc_walshChar S x * khc_walshChar S y) = if x = y then (2 ^ Fintype.card ι : ℝ) else 0 := by
-- proof
  apply StatMech.Probability.khc_sum_walshChar_mul x y

/--
[khc_fourier_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_fourier_expansion_eq
  [Fintype ι]
  [DecidableEq ι]
  {f : (ι → Bool) → ℝ}
  {x : ι → Bool} :
-- imply
  (∑ S : Finset ι, khc_fourierCoeff f S * khc_walshChar S x) = f x := by
-- proof
  apply StatMech.Probability.khc_fourier_expansion f x

/--
[khc_uexp_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_uexp_finset_sum_eq
  [Fintype ι]
  [DecidableEq ι]
  {s : Finset κ}
  {g : κ → (ι → Bool) → ℝ} :
-- imply
  bnt_uexp (fun x => ∑ k ∈ s, g k x) = ∑ k ∈ s, bnt_uexp (g k) := by
-- proof
  apply StatMech.Probability.khc_uexp_finset_sum s g

/--
[khc_uexp_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_uexp_const_mul_eq
  [Fintype ι]
  [DecidableEq ι]
  {c : ℝ}
  {g : (ι → Bool) → ℝ} :
-- imply
  bnt_uexp (fun x => c * g x) = c * bnt_uexp g := by
-- proof
  apply StatMech.Probability.khc_uexp_const_mul c g

/--
[khc_uexp_fourier_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_uexp_fourier_mul_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : Finset ι → ℝ} :
-- imply
  bnt_uexp (fun x => (∑ S : Finset ι, a S * khc_walshChar S x) * (∑ T : Finset ι, b T * khc_walshChar T x)) = ∑ S : Finset ι, a S * b S := by
-- proof
  apply StatMech.Probability.khc_uexp_fourier_mul a b

/--
[khc_parseval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_parseval_eq
  [Fintype ι]
  [DecidableEq ι]
  {f g : (ι → Bool) → ℝ} :
-- imply
  bnt_uexp (fun x => f x * g x) = ∑ S : Finset ι, khc_fourierCoeff f S * khc_fourierCoeff g S := by
-- proof
  apply StatMech.Probability.khc_parseval f g

/--
[khc_parseval_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_parseval_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {f : (ι → Bool) → ℝ} :
-- imply
  bnt_uexp (fun x => (f x) ^ 2) = ∑ S : Finset ι, (khc_fourierCoeff f S) ^ 2 := by
-- proof
  apply StatMech.Probability.khc_parseval_sq f

/--
[khc_noiseOp_walshChar_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_noiseOp_walshChar_apply_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {S : Finset ι}
  {x : ι → Bool} :
-- imply
  bnt_noiseOp ρ (khc_walshChar S) x = ρ ^ S.card * khc_walshChar S x := by
-- proof
  apply StatMech.Probability.khc_noiseOp_walshChar_apply ρ S x

/--
[khc_noiseOp_walshChar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_noiseOp_walshChar_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {S : Finset ι} :
-- imply
  bnt_noiseOp ρ (khc_walshChar S) = fun x => ρ ^ S.card * khc_walshChar S x := by
-- proof
  apply StatMech.Probability.khc_noiseOp_walshChar ρ S

/--
[khc_noiseOp_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_noiseOp_finset_sum_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {s : Finset κ}
  {g : κ → (ι → Bool) → ℝ} :
-- imply
  bnt_noiseOp ρ (fun x => ∑ k ∈ s, g k x) = fun x => ∑ k ∈ s, bnt_noiseOp ρ (g k) x := by
-- proof
  apply StatMech.Probability.khc_noiseOp_finset_sum ρ s g

/--
[khc_noiseOp_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_noiseOp_const_mul_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ c : ℝ}
  {g : (ι → Bool) → ℝ} :
-- imply
  bnt_noiseOp ρ (fun x => c * g x) = fun x => c * bnt_noiseOp ρ g x := by
-- proof
  apply StatMech.Probability.khc_noiseOp_const_mul ρ c g

/--
[khc_noiseOp_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_noiseOp_fourier_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {f : (ι → Bool) → ℝ} :
-- imply
  bnt_noiseOp ρ f = fun x => ∑ S : Finset ι, (ρ ^ S.card * khc_fourierCoeff f S) * khc_walshChar S x := by
-- proof
  apply StatMech.Probability.khc_noiseOp_fourier ρ f

/--
[khc_noiseOp_l2sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_noiseOp_l2sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {f : (ι → Bool) → ℝ} :
-- imply
  bnt_uexp (fun x => (bnt_noiseOp ρ f x) ^ 2) = ∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2 := by
-- proof
  apply StatMech.Probability.khc_noiseOp_l2sq ρ f

/--
[khc_uexp_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_uexp_reindex_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {e : κ ≃ ι}
  {f : (ι → Bool) → ℝ} :
-- imply
  bnt_uexp (khc_reindex e f) = bnt_uexp f := by
-- proof
  apply StatMech.Probability.khc_uexp_reindex e f

/--
[khc_qnorm_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_qnorm_reindex_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {e : κ ≃ ι}
  {q : ℝ}
  {f : (ι → Bool) → ℝ} :
-- imply
  bnt_qnorm q (khc_reindex e f) = bnt_qnorm q f := by
-- proof
  apply StatMech.Probability.khc_qnorm_reindex e q f

/--
[khc_noiseOp_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_noiseOp_reindex_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {e : κ ≃ ι}
  {ρ : ℝ}
  {f : (ι → Bool) → ℝ} :
-- imply
  bnt_noiseOp ρ (khc_reindex e f) = khc_reindex e (bnt_noiseOp ρ f) := by
-- proof
  apply StatMech.Probability.khc_noiseOp_reindex e ρ f

/--
[khc_hypercontractivity_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_hypercontractivity_general_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {g : (ι → Bool) → ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  bnt_qnorm 2 (bnt_noiseOp ρ g) ≤ bnt_qnorm (1 + ρ ^ 2) g := by
-- proof
  apply StatMech.Probability.khc_hypercontractivity_general h0 h1 g

/--
[khc_lowDegreeWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_lowDegreeWeight_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {f : (ι → Bool) → ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2) ≤ (bnt_qnorm (1 + ρ ^ 2) f) ^ 2 := by
-- proof
  apply StatMech.Probability.khc_lowDegreeWeight_le h0 h1 f

/--
[khc_lowDegreeWeight_fluct_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_lowDegreeWeight_fluct_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {f : (ι → Bool) → ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  (∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2) ≤ (bnt_qnorm (1 + ρ ^ 2) f) ^ 2 - (khc_fourierCoeff f ∅) ^ 2 := by
-- proof
  apply StatMech.Probability.khc_lowDegreeWeight_fluct_le h0 h1 f

/--
[khc_bernoulliWeight_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_bernoulliWeight_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {ω : ConfigSpace ι} :
-- imply
  OSSS.weight (OSSS.bernoulliWeight (1 / 2 : ℝ)) ω = 1 / (2 ^ Fintype.card ι) := by
-- proof
  apply StatMech.Probability.khc_bernoulliWeight_half ω

/--
[khc_expect_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_expect_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {g : ConfigSpace ι → ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) g = bnt_uexp g := by
-- proof
  apply StatMech.Probability.khc_expect_half g

/--
[khc_uexp_eq_coeff_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_uexp_eq_coeff_empty_eq
  [Fintype ι]
  [DecidableEq ι]
  {g : ConfigSpace ι → ℝ} :
-- imply
  bnt_uexp g = khc_fourierCoeff g ∅ := by
-- proof
  apply StatMech.Probability.khc_uexp_eq_coeff_empty g

/--
[khc_var_eq_fourierWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_var_eq_fourierWeight_eq
  [Fintype ι]
  [DecidableEq ι]
  {g : ConfigSpace ι → ℝ} :
-- imply
  OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) g = ∑ S ∈ (univ.erase (∅ : Finset ι)), (khc_fourierCoeff g S) ^ 2 := by
-- proof
  apply StatMech.Probability.khc_var_eq_fourierWeight g

/--
[khc_walshChar_setOpen_sub_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_walshChar_setOpen_sub_setClosed_eq
  [Fintype ι]
  [DecidableEq ι]
  {S : Finset ι}
  {e : ι}
  {ω : ConfigSpace ι} :
-- imply
  khc_walshChar S (StatMech.setOpen e ω) - khc_walshChar S (StatMech.setClosed e ω) = if e ∈ S then (-2 : ℝ) * khc_walshChar (S.erase e) ω else 0 := by
-- proof
  apply StatMech.Probability.khc_walshChar_setOpen_sub_setClosed S e ω

/--
[khc_deriv_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_deriv_fourier_eq
  [Fintype ι]
  [DecidableEq ι]
  {g : ConfigSpace ι → ℝ}
  {e : ι}
  {ω : ConfigSpace ι} :
-- imply
  g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω) = ∑ S ∈ univ.filter (fun S => e ∈ S), ((-2 : ℝ) * khc_fourierCoeff g S) * khc_walshChar (S.erase e) ω := by
-- proof
  apply StatMech.Probability.khc_deriv_fourier g e ω

/--
[khc_uexp_sum_walsh_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_uexp_sum_walsh_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {s : Finset (Finset ι)}
  {a : Finset ι → ℝ}
  {T : Finset ι → Finset ι}
-- given
  (hTinj : Set.InjOn T s) :
-- imply
  bnt_uexp (fun x => (∑ S ∈ s, a S * khc_walshChar (T S) x) ^ 2) = ∑ S ∈ s, (a S) ^ 2 := by
-- proof
  apply StatMech.Probability.khc_uexp_sum_walsh_sq s a T hTinj

/--
[khc_erase_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_erase_injOn_eq
  [Fintype ι]
  [DecidableEq ι]
  {e : ι} :
-- imply
  Set.InjOn (fun S => Finset.erase S e) ↑(univ.filter (fun S : Finset ι => e ∈ S)) := by
-- proof
  apply StatMech.Probability.khc_erase_injOn e

/--
[khc_abs_diff_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_abs_diff_indicator_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {e : ι}
  {ω : ConfigSpace ι} :
-- imply
  |(fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω) - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)| = ((fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω) - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)) ^ 2 := by
-- proof
  apply StatMech.Probability.khc_abs_diff_indicator φ e ω

/--
[khc_infl_eq_fourierWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_infl_eq_fourierWeight_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {e : ι} :
-- imply
  OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e = ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), 4 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.khc_infl_eq_fourierWeight φ e

/--
[khc_totalInfl_eq_fourierWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_totalInfl_eq_fourierWeight_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) = ∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.khc_totalInfl_eq_fourierWeight φ

/--
[khc_logSobolevStep_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_logSobolevStep_zero_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  khc_LogSobolevStep 0 := by
-- proof
  apply StatMech.Probability.khc_logSobolevStep_zero

/--
[khc_KKL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean)
-/
@[path]
private lemma khc_KKL_eq
  [Fintype ι]
  [DecidableEq ι]
  {c : ℝ}
  {H : khc_LogSobolevStep c} :
-- imply
  KKLHypercontractive (1 / 2 : ℝ) c := by
-- proof
  apply StatMech.Probability.khc_KKL H


-- created on 2026-10-23
