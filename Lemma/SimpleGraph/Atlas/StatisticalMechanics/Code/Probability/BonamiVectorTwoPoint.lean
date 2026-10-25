import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.BonamiVectorTwoPoint
open Finset StatMech StatMech.Probability


/--
[bvtp_uexp_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_uexp_add_eq
  [Fintype ι]
  [DecidableEq ι]
-- given
  (g h : (ι → Bool) → ℝ) :
-- imply
  bnt_uexp (fun ω => g ω + h ω) = bnt_uexp g + bnt_uexp h := by
-- proof
  apply StatMech.Probability.bvtp_uexp_add g h

/--
[bvtp_uexp_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_uexp_smul_eq
  [Fintype ι]
  [DecidableEq ι]
  {c : ℝ}
  {g : (ι → Bool) → ℝ} :
-- imply
  bnt_uexp (fun ω => c * g ω) = c * bnt_uexp g := by
-- proof
  apply StatMech.Probability.bvtp_uexp_smul c g

/--
[bvtp_qnormPow2_eq_uexp_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_qnormPow2_eq_uexp_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {f : (ι → Bool) → ℝ} :
-- imply
  bnt_qnormPow 2 f = bnt_uexp (fun ω => (f ω) ^ 2) := by
-- proof
  apply StatMech.Probability.bvtp_qnormPow2_eq_uexp_sq f

/--
[bvtp_qnorm2_eq_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_qnorm2_eq_sqrt_eq
  [Fintype ι]
  [DecidableEq ι]
  {u : (ι → Bool) → ℝ} :
-- imply
  bnt_qnorm 2 u = Real.sqrt (bnt_qnormPow 2 u) := by
-- proof
  apply StatMech.Probability.bvtp_qnorm2_eq_sqrt u

/--
[bvtp_qnorm2_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_qnorm2_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {u : (ι → Bool) → ℝ} :
-- imply
  (bnt_qnorm 2 u) ^ 2 = bnt_qnormPow 2 u := by
-- proof
  apply StatMech.Probability.bvtp_qnorm2_sq u

/--
[bvtp_qnormPow2_expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_qnormPow2_expand_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ℝ}
  {u v : (ι → Bool) → ℝ} :
-- imply
  bnt_qnormPow 2 (fun ω => a * u ω + b * v ω) = a ^ 2 * bnt_uexp (fun ω => (u ω) ^ 2) + 2 * a * b * bnt_uexp (fun ω => u ω * v ω) + b ^ 2 * bnt_uexp (fun ω => (v ω) ^ 2) := by
-- proof
  apply StatMech.Probability.bvtp_qnormPow2_expand a b u v

/--
[bvtp_uexp_inner_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_uexp_inner_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {u v : (ι → Bool) → ℝ} :
-- imply
  bnt_uexp (fun ω => u ω * v ω) ≤ bnt_qnorm 2 u * bnt_qnorm 2 v := by
-- proof
  apply StatMech.Probability.bvtp_uexp_inner_le u v

/--
[bvtp_vectorTwoPoint_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_vectorTwoPoint_aux_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {n : ℕ}
  {u v : (Fin n → Bool) → ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  (bnt_qnormPow 2 (fun ω => (1 + ρ) / 2 * u ω + (1 - ρ) / 2 * v ω) + bnt_qnormPow 2 (fun ω => (1 - ρ) / 2 * u ω + (1 + ρ) / 2 * v ω)) / 2 ≤ ((bnt_qnorm 2 u ^ (1 + ρ ^ 2) + bnt_qnorm 2 v ^ (1 + ρ ^ 2)) / 2) ^ (2 / (1 + ρ ^ 2)) := by
-- proof
  apply StatMech.Probability.bvtp_vectorTwoPoint_aux h0 h1 n u v

/--
[bvtp_vectorTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_vectorTwoPoint_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  bnt_VectorTwoPoint ρ := by
-- proof
  apply StatMech.Probability.bvtp_vectorTwoPoint h0 h1

/--
[bvtp_tensorStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_tensorStep_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  bnt_TensorStep ρ := by
-- proof
  apply StatMech.Probability.bvtp_tensorStep h0 h1

/--
[bvtp_hypercontractivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean)
-/
@[path]
private lemma bvtp_hypercontractivity_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
-- proof
  apply StatMech.Probability.bvtp_hypercontractivity h0 h1 n f


-- created on 2026-10-23
