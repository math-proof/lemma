import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.WeightedFieldGhost.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Sharpness StatMech.Sharpness.WeightedFieldGhost


/--
[weightedZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
-- given
  (J : Sym2 V -> ℝ)
  (h : ℝ) :
-- imply
  0 < weightedZ G β J h := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedZ_pos G β J h

/--
[weightedZ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedZ_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
-- given
  (J : Sym2 V -> ℝ)
  (h : ℝ) :
-- imply
  weightedZ G β J h ≠ 0 := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedZ_ne_zero G β J h

/--
[ghost_weight_eq_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma ghost_weight_eq_weighted_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace (Option V)}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ) :
-- imply
  boltzmannJ (withGhost G) β (ghostCoupling h β J) s = weightedWeight G β J (h * spin s none) (fun z => s (some z)) := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.ghost_weight_eq_weighted G β h J s

/--
[weightedEnergy_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedEnergy_flip_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
-- given
  (J : Sym2 V -> ℝ)
  (h : ℝ) :
-- imply
  weightedEnergy G J (-h) (flipV s) = weightedEnergy G J h s := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedEnergy_flip G J h s

/--
[weightedWeight_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedWeight_flip_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ) :
-- imply
  weightedWeight G β J (-h) (flipV s) = weightedWeight G β J h s := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedWeight_flip G β h J s

/--
[weightedZ_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedZ_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ) :
-- imply
  weightedZ G β J (-h) = weightedZ G β J h := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedZ_neg G β h J

/--
[weightedNum_neg_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedNum_neg_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (hA : Even A.card) :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J (-h) s) = ∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J h s := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedNum_neg_even G β h J A hA

/--
[weightedNum_neg_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedNum_neg_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (hA : Odd A.card) :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J (-h) s) = -∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J h s := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedNum_neg_odd G β h J A hA

/--
[partition_ghost_eq_weightedZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma partition_ghost_eq_weightedZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ) :
-- imply
  partitionJ (withGhost G) β (ghostCoupling h β J) = 2 * weightedZ G β J h := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.partition_ghost_eq_weightedZ G β h J

/--
[num_ghost_eq_weighted_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma num_ghost_eq_weighted_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (hA : Even A.card) :
-- imply
  (∑ s : ConfigSpace (Option V), spinProd (A.map someEmb) s * boltzmannJ (withGhost G) β (ghostCoupling h β J) s) = 2 * ∑ t : ConfigSpace V, spinProd A t * weightedWeight G β J h t := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.num_ghost_eq_weighted_even G β h J A hA

/--
[num_ghost_eq_weighted_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma num_ghost_eq_weighted_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (hA : Odd A.card) :
-- imply
  (∑ s : ConfigSpace (Option V), spinProd (insert none (A.map someEmb)) s * boltzmannJ (withGhost G) β (ghostCoupling h β J) s) = 2 * ∑ t : ConfigSpace V, spinProd A t * weightedWeight G β J h t := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.num_ghost_eq_weighted_odd G β h J A hA

/--
[weightedExpectation_eq_currentRatio_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedExpectation_eq_currentRatio_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (hA : Even A.card) :
-- imply
  weightedExpectation G β J h (spinProd A) = currentSum (withGhost G) β (ghostCoupling h β J) (A.map someEmb) / currentSum (withGhost G) β (ghostCoupling h β J) ∅ := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedExpectation_eq_currentRatio_even G β h J A hA

/--
[weightedExpectation_eq_currentRatio_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedExpectation_eq_currentRatio_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (hA : Odd A.card) :
-- imply
  weightedExpectation G β J h (spinProd A) = currentSum (withGhost G) β (ghostCoupling h β J) (insert none (A.map someEmb)) / currentSum (withGhost G) β (ghostCoupling h β J) ∅ := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedExpectation_eq_currentRatio_odd G β h J A hA

/--
[hasDerivAt_weightedWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma hasDerivAt_weightedWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ) :
-- imply
  HasDerivAt (fun β => weightedWeight G β J h s) (weightedWeight G β J h s * weightedEnergy G J h s) β := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.hasDerivAt_weightedWeight G β h J s

/--
[hasDerivAt_weightedNum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma hasDerivAt_weightedNum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (f : ConfigSpace V -> ℝ) :
-- imply
  HasDerivAt (fun β => ∑ s : ConfigSpace V, f s * weightedWeight G β J h s) (∑ s : ConfigSpace V, f s * (weightedWeight G β J h s * weightedEnergy G J h s)) β := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.hasDerivAt_weightedNum G β h J f

/--
[hasDerivAt_weightedZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma hasDerivAt_weightedZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ) :
-- imply
  HasDerivAt (fun β => weightedZ G β J h) (∑ s : ConfigSpace V, weightedWeight G β J h s * weightedEnergy G J h s) β := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.hasDerivAt_weightedZ G β h J

/--
[hasDerivAt_weightedExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma hasDerivAt_weightedExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (f : ConfigSpace V -> ℝ) :
-- imply
  HasDerivAt (fun β => weightedExpectation G β J h f) (weightedExpectation G β J h (fun s => f s * weightedEnergy G J h s) - weightedExpectation G β J h f * weightedExpectation G β J h (weightedEnergy G J h)) β := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.hasDerivAt_weightedExpectation G β h J f

/--
[weightedExpectation_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedExpectation_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset ι}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (f : ι -> ConfigSpace V -> ℝ) :
-- imply
  weightedExpectation G β J h (fun s => ∑ i ∈ S, f i s) = ∑ i ∈ S, weightedExpectation G β J h (f i) := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedExpectation_sum G β h J S f

/--
[weightedExpectation_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedExpectation_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (f g : ConfigSpace V -> ℝ) :
-- imply
  weightedExpectation G β J h (fun s => f s + g s) = weightedExpectation G β J h f + weightedExpectation G β J h g := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedExpectation_add G β h J f g

/--
[weightedExpectation_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedExpectation_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h c : ℝ)
  (J : Sym2 V -> ℝ)
  (f : ConfigSpace V -> ℝ) :
-- imply
  weightedExpectation G β J h (fun s => c * f s) = c * weightedExpectation G β J h f := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedExpectation_const_mul G β h c J f

/--
[hasDerivAt_weightedMagnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma hasDerivAt_weightedMagnetization_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ) :
-- imply
  HasDerivAt (fun β => weightedExpectation G β J h (fun s => spin s o)) ((∑ e ∈ G.edgeFinset, J e * (weightedExpectation G β J h (fun s => spin s o * bond s e) - weightedExpectation G β J h (fun s => spin s o) * weightedExpectation G β J h (fun s => bond s e))) + h * ∑ z, (weightedExpectation G β J h (fun s => spin s o * spin s z) - weightedExpectation G β J h (fun s => spin s o) * weightedExpectation G β J h (fun s => spin s z))) β := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.hasDerivAt_weightedMagnetization G β h J o

/--
[weightedBond_covariance_sourcePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedBond_covariance_sourcePair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (hxy : x ≠ y) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 * (weightedExpectation G β J h (spinProd (({o} : Finset V) ∆ {x, y})) - weightedExpectation G β J h (spinProd ({x, y} : Finset V)) * weightedExpectation G β J h (spinProd ({o} : Finset V))) = weightedBondDelta G β h J o s(x, y) := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedBond_covariance_sourcePair G β h J o x y hxy

/--
[weightedField_covariance_sourcePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedField_covariance_sourcePair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o z : V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 * (weightedExpectation G β J h (spinProd (({o} : Finset V) ∆ {z})) - weightedExpectation G β J h (spinProd ({z} : Finset V)) * weightedExpectation G β J h (spinProd ({o} : Finset V))) = weightedFieldDelta G β h J o z := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedField_covariance_sourcePair G β h J o z

/--
[weightedBond_covariance_eq_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedBond_covariance_eq_delta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {e : Sym2 V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (he : e ∈ G.edgeFinset) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 * (weightedExpectation G β J h (fun s => spin s o * bond s e) - weightedExpectation G β J h (fun s => spin s o) * weightedExpectation G β J h (fun s => bond s e)) = weightedBondDelta G β h J o e := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedBond_covariance_eq_delta G β h J o e he

/--
[weightedField_covariance_eq_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedField_covariance_eq_delta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o z : V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 * (weightedExpectation G β J h (fun s => spin s o * spin s z) - weightedExpectation G β J h (fun s => spin s o) * weightedExpectation G β J h (fun s => spin s z)) = weightedFieldDelta G β h J o z := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedField_covariance_eq_delta G β h J o z

/--
[weighted_deriv_magnetization_eq_currentDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weighted_deriv_magnetization_eq_currentDelta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ) :
-- imply
  HasDerivAt (fun β => weightedExpectation G β J h (fun s => spin s o)) ((1 / (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2) * ((∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) + h * ∑ z, weightedFieldDelta G β h J o z)) β := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weighted_deriv_magnetization_eq_currentDelta G β h J o

/--
[weightedBondDelta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedBondDelta_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {e : Sym2 V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ weightedBondDelta G β h J o e := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedBondDelta_nonneg G β h J hβ hh hJ o e

/--
[weightedFieldDelta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weightedFieldDelta_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o z : V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ weightedFieldDelta G β h J o z := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weightedFieldDelta_nonneg G β h J hβ hh hJ o z

/--
[weighted_currentDelta_derivative_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean)
-/
@[path]
private lemma weighted_currentDelta_derivative_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (J : Sym2 V -> ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ (1 / (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2) * ((∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) + h * ∑ z, weightedFieldDelta G β h J o z) := by
-- proof
  apply StatMech.Sharpness.WeightedFieldGhost.weighted_currentDelta_derivative_nonneg G β h J hβ hh hJ o


-- created on 2026-10-23
