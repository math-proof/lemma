import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewrite
open Finset SimpleGraph Set StatMech StatMech.Sharpness


/--
[sdr_hasDerivAt_isingWeight_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_hasDerivAt_isingWeight_beta_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => isingWeight G β h s) (isingWeight G β h s * (sdrBondEnergy G s + h * sdrTotalSpin s)) β := by
-- proof
  apply StatMech.Sharpness.sdr_hasDerivAt_isingWeight_beta β h s

/--
[sdr_hasDerivAt_num_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_hasDerivAt_num_beta_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => ∑ s : ConfigSpace V, f s * isingWeight G β h s) (∑ s : ConfigSpace V, f s * (isingWeight G β h s * (sdrBondEnergy G s + h * sdrTotalSpin s))) β := by
-- proof
  apply StatMech.Sharpness.sdr_hasDerivAt_num_beta β h f

/--
[sdr_hasDerivAt_isingZ_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_hasDerivAt_isingZ_beta_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => isingZ G β h) (∑ s : ConfigSpace V, isingWeight G β h s * (sdrBondEnergy G s + h * sdrTotalSpin s)) β := by
-- proof
  apply StatMech.Sharpness.sdr_hasDerivAt_isingZ_beta β h

/--
[sdr_expectation_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_expectation_eq_div_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h f = (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h := by
-- proof
  apply StatMech.Sharpness.sdr_expectation_eq_div β h f

/--
[sdr_hasDerivAt_expectation_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_hasDerivAt_expectation_beta_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => isingExpectation G β h f) (isingExpectation G β h (fun s => f s * (sdrBondEnergy G s + h * sdrTotalSpin s)) - isingExpectation G β h f * isingExpectation G β h (fun s => sdrBondEnergy G s + h * sdrTotalSpin s)) β := by
-- proof
  apply StatMech.Sharpness.sdr_hasDerivAt_expectation_beta β h f

/--
[sdr_expectation_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_expectation_sum_eq
  [Fintype V]
  [DecidableEq V]
  {s : Finset ι}
  {f : ι → ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun cfg => ∑ i ∈ s, f i cfg) = ∑ i ∈ s, isingExpectation G β h (f i) := by
-- proof
  apply StatMech.Sharpness.sdr_expectation_sum β h s f

/--
[sdr_expectation_mul_bondEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_expectation_mul_bondEnergy_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => f s * sdrBondEnergy G s) = ∑ e ∈ G.edgeFinset, isingExpectation G β h (fun s => f s * bond s e) := by
-- proof
  apply StatMech.Sharpness.sdr_expectation_mul_bondEnergy β h f

/--
[sdr_expectation_bondEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_expectation_bondEnergy_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (sdrBondEnergy G) = ∑ e ∈ G.edgeFinset, isingExpectation G β h (fun s => bond s e) := by
-- proof
  apply StatMech.Sharpness.sdr_expectation_bondEnergy β h

/--
[sdr_expectation_mul_totalSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_expectation_mul_totalSpin_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => f s * sdrTotalSpin s) = ∑ z, isingExpectation G β h (fun s => f s * spin s z) := by
-- proof
  apply StatMech.Sharpness.sdr_expectation_mul_totalSpin β h f

/--
[sdr_expectation_totalSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_expectation_totalSpin_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h sdrTotalSpin = ∑ z, isingExpectation G β h (fun s => spin s z) := by
-- proof
  apply StatMech.Sharpness.sdr_expectation_totalSpin β h

/--
[sdr_deriv_magnetization_eq_bondCov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_deriv_magnetization_eq_bondCov_eq
  [Fintype V]
  [DecidableEq V]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => isingExpectation G β h (fun s => spin s o)) ((∑ e ∈ G.edgeFinset, (isingExpectation G β h (fun s => spin s o * bond s e) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => bond s e))) + h * ∑ z, (isingExpectation G β h (fun s => spin s o * spin s z) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s z))) β := by
-- proof
  apply StatMech.Sharpness.sdr_deriv_magnetization_eq_bondCov β h o

/--
[sdr_deltaIndicator_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_deltaIndicator_split_eq
  [Fintype V]
  [DecidableEq V]
  {D P Q : Prop}
  [Decidable D]
  [Decidable P]
  [Decidable Q]
-- given
  (hdich : D → (P ↔ ¬ Q)) :
-- imply
  (if D then (1 : ℝ) else 0) = (if D ∧ P then 1 else 0) + (if D ∧ Q then 1 else 0) := by
-- proof
  apply StatMech.Sharpness.sdr_deltaIndicator_split hdich

/--
[sdr_deltaRewrite_perEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_deltaRewrite_perEdge_eq
  [Fintype V]
  [DecidableEq V]
  {covTerm : ℝ}
  [DecidablePred disconn]
  [DecidablePred caseA]
  [DecidablePred caseB]
  [DecidablePred (fun m => (disconn m ∧ caseA m) ∨ (disconn m ∧ caseB m))]
-- given
  (pairSum : (Cur → Prop) → ℝ)
  (hpairSum_add : ∀ (P₁ P₂ : Cur → Prop) [DecidablePred P₁] [DecidablePred P₂] [DecidablePred (fun m => P₁ m ∨ P₂ m)], (∀ m, ¬ (P₁ m ∧ P₂ m)) → pairSum (fun m => P₁ m ∨ P₂ m) = pairSum P₁ + pairSum P₂)
  (disconn caseA caseB : Cur → Prop)
  (hcov : covTerm = pairSum disconn)
  (hdich : ∀ m, disconn m → (caseA m ↔ ¬ caseB m)) :
-- imply
  covTerm = pairSum (fun m => disconn m ∧ caseA m) + pairSum (fun m => disconn m ∧ caseB m) := by
-- proof
  apply StatMech.Sharpness.sdr_deltaRewrite_perEdge covTerm pairSum hpairSum_add disconn caseA caseB hcov hdich

/--
[sdr_indicatorPairSum_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean)
-/
@[path]
private lemma sdr_indicatorPairSum_add_eq
  [Fintype V]
  [DecidableEq V]
  {W : (Cur × Cur) → ℝ}
  {Z2 : ℝ}
  {sup : (Cur × Cur) → Cur}
  [DecidablePred P₁]
  [DecidablePred P₂]
  [DecidablePred (fun m => P₁ m ∨ P₂ m)]
-- given
  (P₁ P₂ : Cur → Prop)
  (hsummable : Summable (fun pq : Cur × Cur => W pq))
  (hdisj : ∀ m, ¬ (P₁ m ∧ P₂ m)) :
-- imply
  (1 / Z2) * ∑' pq : Cur × Cur, W pq * (if (fun m => P₁ m ∨ P₂ m) (sup pq) then 1 else 0) = ((1 / Z2) * ∑' pq : Cur × Cur, W pq * (if P₁ (sup pq) then 1 else 0)) + ((1 / Z2) * ∑' pq : Cur × Cur, W pq * (if P₂ (sup pq) then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.sdr_indicatorPairSum_add W Z2 sup P₁ P₂ hsummable hdisj


-- created on 2026-10-23
