import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
open Finset StatMech StatMech.FK


/--
[betaParams_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma betaParams_pos_eq
  [Fintype V]
  [DecidableEq V]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {e : Sym2 V}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β) :
-- imply
  0 < betaParams J β e := by
-- proof
  apply StatMech.FK.betaParams_pos hJ hβ e

/--
[betaParams_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma betaParams_lt_one_eq
  [Fintype V]
  [DecidableEq V]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {e : Sym2 V} :
-- imply
  betaParams J β e < 1 := by
-- proof
  apply StatMech.FK.betaParams_lt_one J β e

/--
[hasDerivAt_betaFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma hasDerivAt_betaFactor_eq
  [Fintype V]
  [DecidableEq V]
  {J : Sym2 V → ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
  {β : ℝ} :
-- imply
  HasDerivAt (fun b => if ω e then betaParams J b e else 1 - betaParams J b e) (if ω e then J e * Real.exp (-(β * J e)) else -(J e * Real.exp (-(β * J e)))) β := by
-- proof
  apply StatMech.FK.hasDerivAt_betaFactor J ω e β

/--
[betaFactor_deriv_eq_mul_score](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma betaFactor_deriv_eq_mul_score_eq
  [Fintype V]
  [DecidableEq V]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β) :
-- imply
  (if ω e then J e * Real.exp (-(β * J e)) else -(J e * Real.exp (-(β * J e)))) = (if ω e then betaParams J β e else 1 - betaParams J β e) * ((J e / betaParams J β e) * (coordR e ω - betaParams J β e)) := by
-- proof
  apply StatMech.FK.betaFactor_deriv_eq_mul_score hJ hβ ω e

/--
[hasDerivAt_edgeProductW_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma hasDerivAt_edgeProductW_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β) :
-- imply
  HasDerivAt (fun b => edgeProductW G (betaParams J b) ω) (edgeProductW G (betaParams J β) ω * betaScore G J β ω) β := by
-- proof
  apply StatMech.FK.hasDerivAt_edgeProductW_beta G hJ hβ ω

/--
[hasDerivAt_fkWeightW_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma hasDerivAt_fkWeightW_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β) :
-- imply
  HasDerivAt (fun b => fkWeightW G (betaParams J b) q ω) (fkWeightW G (betaParams J β) q ω * betaScore G J β ω) β := by
-- proof
  apply StatMech.FK.hasDerivAt_fkWeightW_beta G hJ hβ q ω

/--
[hasDerivAt_fkNumerW_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma hasDerivAt_fkNumerW_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β) :
-- imply
  HasDerivAt (fun b => fkNumerW G (betaParams J b) q g) (fkNumerW G (betaParams J β) q (fun ω => g ω * betaScore G J β ω)) β := by
-- proof
  apply StatMech.FK.hasDerivAt_fkNumerW_beta G hJ hβ q g

/--
[fkCovW_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma fkCovW_zero_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  fkCovW G pf q g (fun _ => 0) = 0 := by
-- proof
  apply StatMech.FK.fkCovW_zero_right G pf q g

/--
[fkCovW_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma fkCovW_add_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
-- given
  (g h k : ConfigSpace (Sym2 V) → ℝ) :
-- imply
  fkCovW G pf q g (fun ω => h ω + k ω) = fkCovW G pf q g h + fkCovW G pf q g k := by
-- proof
  apply StatMech.FK.fkCovW_add_right G pf q g h k

/--
[fkCovW_const_mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma fkCovW_const_mul_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q c : ℝ}
-- given
  (g h : ConfigSpace (Sym2 V) → ℝ) :
-- imply
  fkCovW G pf q g (fun ω => c * h ω) = c * fkCovW G pf q g h := by
-- proof
  apply StatMech.FK.fkCovW_const_mul_right G pf q c g h

/--
[fkCovW_finset_sum_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma fkCovW_finset_sum_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
  {s : Finset ι}
-- given
  (h : ι → ConfigSpace (Sym2 V) → ℝ) :
-- imply
  fkCovW G pf q g (fun ω => ∑ i ∈ s, h i ω) = ∑ i ∈ s, fkCovW G pf q g (h i) := by
-- proof
  apply StatMech.FK.fkCovW_finset_sum_right G pf q g s h

/--
[fkCovW_betaScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma fkCovW_betaScore_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hq : 0 < q) :
-- imply
  fkCovW G (betaParams J β) q g (betaScore G J β) = ∑ e ∈ G.edgeFinset, (J e / betaParams J β e) * fkCovW G (betaParams J β) q g (coordR e) := by
-- proof
  apply StatMech.FK.fkCovW_betaScore G hJ hβ hq g

/--
[hasDerivAt_fkMeanW_beta_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma hasDerivAt_fkMeanW_beta_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun b => fkMeanW G (betaParams J b) q g) (∑ e ∈ G.edgeFinset, (J e / betaParams J β e) * fkCovW G (betaParams J β) q g (coordR e)) β := by
-- proof
  apply StatMech.FK.hasDerivAt_fkMeanW_beta_sum G hJ hβ hq g

/--
[hasDerivAt_fkProbWOf_beta_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean)
-/
@[path]
private lemma hasDerivAt_fkProbWOf_beta_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun b => fkProbWOf G (betaParams J b) q A) (∑ e ∈ G.edgeFinset, (J e / (1 - Real.exp (-(β * J e)))) * fkCovW G (betaParams J β) q (A.indicator (fun _ => (1 : ℝ))) (coordR e)) β := by
-- proof
  apply StatMech.FK.hasDerivAt_fkProbWOf_beta_sum G hJ hβ hq A


-- created on 2026-10-23
