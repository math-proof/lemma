import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.BonamiTensorize.Part4
open Finset StatMech StatMech.Probability


/--
[bnt_qnormPow_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_qnormPow_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {f : (ι → Bool) → ℝ} :
-- imply
  0 ≤ bnt_qnormPow q f := by
-- proof
  apply StatMech.Probability.bnt_qnormPow_nonneg q f

/--
[bnt_qnorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_qnorm_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {f : (ι → Bool) → ℝ} :
-- imply
  0 ≤ bnt_qnorm q f := by
-- proof
  apply StatMech.Probability.bnt_qnorm_nonneg q f

/--
[bnt_noiseOp_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_noiseOp_one_eq
  [Fintype ι]
  [DecidableEq ι]
  {f : (ι → Bool) → ℝ}
  {x : ι → Bool} :
-- imply
  bnt_noiseOp 1 f x = f x := by
-- proof
  apply StatMech.Probability.bnt_noiseOp_one f x

/--
[bnt_sum_cons_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_sum_cons_split_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  [AddCommMonoid M]
  {F : (Fin (n + 1) → Bool) → M} :
-- imply
  (∑ y : Fin (n + 1) → Bool, F y) = ∑ c : Bool, ∑ ω' : Fin n → Bool, F (Fin.cons c ω') := by
-- proof
  apply StatMech.Probability.bnt_sum_cons_split F

/--
[bnt_uexp_cons_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_uexp_cons_split_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → ℝ} :
-- imply
  bnt_uexp f = (∑ c : Bool, bnt_uexp (fun ω' : Fin n → Bool => f (Fin.cons c ω'))) / 2 := by
-- proof
  apply StatMech.Probability.bnt_uexp_cons_split f

/--
[bnt_noiseOp_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_noiseOp_cons_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin (n + 1) → Bool) → ℝ}
  {a : Bool}
  {ω : Fin n → Bool} :
-- imply
  bnt_noiseOp ρ f (Fin.cons a ω) = ∑ c : Bool, (if a = c then (1 + ρ) / 2 else (1 - ρ) / 2) * bnt_noiseOp ρ (fun ω' : Fin n → Bool => f (Fin.cons c ω')) ω := by
-- proof
  apply StatMech.Probability.bnt_noiseOp_cons ρ f a ω

/--
[bnt_qnormPow_cons_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_qnormPow_cons_split_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {q : ℝ}
  {f : (Fin (n + 1) → Bool) → ℝ} :
-- imply
  bnt_qnormPow q f = (∑ c : Bool, bnt_qnormPow q (fun ω' : Fin n → Bool => f (Fin.cons c ω'))) / 2 := by
-- proof
  apply StatMech.Probability.bnt_qnormPow_cons_split q f

/--
[bnt_noiseOp_cons_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_noiseOp_cons_false_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin (n + 1) → Bool) → ℝ}
  {ω : Fin n → Bool} :
-- imply
  bnt_noiseOp ρ f (Fin.cons false ω) = (1 + ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons false ω')) ω + (1 - ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons true ω')) ω := by
-- proof
  apply StatMech.Probability.bnt_noiseOp_cons_false ρ f ω

/--
[bnt_noiseOp_cons_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_noiseOp_cons_true_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin (n + 1) → Bool) → ℝ}
  {ω : Fin n → Bool} :
-- imply
  bnt_noiseOp ρ f (Fin.cons true ω) = (1 - ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons false ω')) ω + (1 + ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons true ω')) ω := by
-- proof
  apply StatMech.Probability.bnt_noiseOp_cons_true ρ f ω

/--
[bnt_qnorm_rpow_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_qnorm_rpow_self_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {q : ℝ}
  {g : (Fin n → Bool) → ℝ}
-- given
  (hq : q ≠ 0) :
-- imply
  bnt_qnorm q g ^ q = bnt_qnormPow q g := by
-- proof
  apply StatMech.Probability.bnt_qnorm_rpow_self hq g

/--
[bnt_qnorm_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_qnorm_add_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {p : ℝ}
  {u v : (Fin n → Bool) → ℝ}
-- given
  (hp : 1 ≤ p) :
-- imply
  bnt_qnorm p (fun ω => u ω + v ω) ≤ bnt_qnorm p u + bnt_qnorm p v := by
-- proof
  apply StatMech.Probability.bnt_qnorm_add_le hp u v

/--
[bnt_qnorm_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_qnorm_const_mul_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ}
  {p : ℝ}
  {c : ℝ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hp : 0 < p) :
-- imply
  bnt_qnorm p (fun ω => c * f ω) = := by
-- proof
  apply StatMech.Probability.bnt_qnorm_const_mul hp c f

/--
[bnt_vectorTwoPoint_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_vectorTwoPoint_zero_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  bnt_VectorTwoPoint 0 := by
-- proof
  apply StatMech.Probability.bnt_vectorTwoPoint_zero

/--
[bnt_vectorTwoPoint_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_vectorTwoPoint_one_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  bnt_VectorTwoPoint 1 := by
-- proof
  apply StatMech.Probability.bnt_vectorTwoPoint_one

/--
[bnt_tensorStep_of_vec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_tensorStep_of_vec_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {Hvec : bnt_VectorTwoPoint ρ}
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → ℝ}
-- given
  (ih : ∀ g : (Fin n → Bool) → ℝ, bnt_qnorm 2 (bnt_noiseOp ρ g) ≤ bnt_qnorm (1 + ρ ^ 2) g) :
-- imply
  bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
-- proof
  apply StatMech.Probability.bnt_tensorStep_of_vec Hvec n ih f

/--
[bnt_TensorStep_of_vectorTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_TensorStep_of_vectorTwoPoint_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {Hvec : bnt_VectorTwoPoint ρ} :
-- imply
  bnt_TensorStep ρ := by
-- proof
  apply StatMech.Probability.bnt_TensorStep_of_vectorTwoPoint Hvec

/--
[bnt_tensorStep_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_tensorStep_one_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  bnt_TensorStep 1 := by
-- proof
  apply StatMech.Probability.bnt_tensorStep_one

/--
[bnt_qnorm_fin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_qnorm_fin_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {f : (Fin 0 → Bool) → ℝ}
-- given
  (hq : 0 < q) :
-- imply
  bnt_qnorm q f = := by
-- proof
  apply StatMech.Probability.bnt_qnorm_fin_zero hq f

/--
[bnt_noiseOp_fin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_noiseOp_fin_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {f : (Fin 0 → Bool) → ℝ} :
-- imply
  bnt_noiseOp ρ f = f := by
-- proof
  apply StatMech.Probability.bnt_noiseOp_fin_zero ρ f

/--
[bnt_hypercontractivity_fin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_hypercontractivity_fin_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {f : (Fin 0 → Bool) → ℝ} :
-- imply
  bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
-- proof
  apply StatMech.Probability.bnt_hypercontractivity_fin_zero ρ f

/--
[bnt_hypercontractivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_hypercontractivity_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {Hvec : bnt_VectorTwoPoint ρ}
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
-- proof
  apply StatMech.Probability.bnt_hypercontractivity Hvec n f

/--
[bnt_hypercontractivity_of_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean)
-/
@[path]
private lemma bnt_hypercontractivity_of_twoPoint_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {Hstep : bnt_TensorStep ρ}
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
-- proof
  apply StatMech.Probability.bnt_hypercontractivity_of_twoPoint Hstep n f


-- created on 2026-10-23
