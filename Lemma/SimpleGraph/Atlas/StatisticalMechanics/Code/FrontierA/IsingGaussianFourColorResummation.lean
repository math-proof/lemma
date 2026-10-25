import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorResummation.Part3
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[finiteTreeFourCurrentPattern_resum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean)
-/
@[path]
private lemma finiteTreeFourCurrentPattern_resum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (P : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> Prop)
  (hsum : Summable (finiteTreeFourCurrentPatternSummand G beta J P))
  (hnonneg : ∀ z, 0 <= finiteTreeFourCurrentPatternSummand G beta J P z) :
-- imply
  Summable (fun total : G.edgeFinset -> Nat => finiteTreeFourColorCoefficient G total P * weight G beta J (ofEdgeFun G total)) ∧ (∑' z, finiteTreeFourCurrentPatternSummand G beta J P z) = ∑' total : G.edgeFinset -> Nat, finiteTreeFourColorCoefficient G total P * weight G beta J (ofEdgeFun G total) := by
-- proof
  apply StatMech.FrontierA.finiteTreeFourCurrentPattern_resum G beta J P hsum hnonneg

/--
[finiteTreeMixedFourMass_resum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean)
-/
@[path]
private lemma finiteTreeMixedFourMass_resum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  Summable (fun total : G.edgeFinset -> Nat => finiteTreeFourColorCoefficient G total (finiteTreeMixedCurrentPattern G i j k l) * weight G beta J (ofEdgeFun G total)) ∧ finiteTreeMixedFourMass G beta J i j k l = ∑' total : G.edgeFinset -> Nat, finiteTreeFourColorCoefficient G total (finiteTreeMixedCurrentPattern G i j k l) * weight G beta J (ofEdgeFun G total) := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedFourMass_resum G beta J hbeta hJ hij hkl

/--
[finiteTreeSeparatedFourMass_resum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean)
-/
@[path]
private lemma finiteTreeSeparatedFourMass_resum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
  {y : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  Summable (fun total : G.edgeFinset -> Nat => finiteTreeFourColorCoefficient G total (finiteTreeSeparatedCurrentPattern G i j k l y) * weight G beta J (ofEdgeFun G total)) ∧ finiteTreeSeparatedFourMass G beta J i j k l y = ∑' total : G.edgeFinset -> Nat, finiteTreeFourColorCoefficient G total (finiteTreeSeparatedCurrentPattern G i j k l y) * weight G beta J (ofEdgeFun G total) := by
-- proof
  apply StatMech.FrontierA.finiteTreeSeparatedFourMass_resum G beta J hbeta hJ hij hkl y

/--
[finiteTreeMixedFourColorCoefficient_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean)
-/
@[path]
private lemma finiteTreeMixedFourColorCoefficient_eq_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (total : G.edgeFinset -> Nat) :
-- imply
  finiteTreeFourColorCoefficient G total (finiteTreeMixedCurrentPattern G i j k l) = (#(finiteTreeMixedColorings (endsM G total) Finset.univ i j k l) : Real) := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedFourColorCoefficient_eq_card G total i j k l

/--
[finiteTreeSeparatedFourColorCoefficient_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean)
-/
@[path]
private lemma finiteTreeSeparatedFourColorCoefficient_eq_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l y : V}
-- given
  (total : G.edgeFinset -> Nat) :
-- imply
  finiteTreeFourColorCoefficient G total (finiteTreeSeparatedCurrentPattern G i j k l y) = (#(finiteTreeSeparatedBranchColorings (endsM G total) Finset.univ i j k l y) : Real) := by
-- proof
  apply StatMech.FrontierA.finiteTreeSeparatedFourColorCoefficient_eq_card G total i j k l y

/--
[finiteTreeMixedFourMass_eq_card_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean)
-/
@[path]
private lemma finiteTreeMixedFourMass_eq_card_tsum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  Summable (fun total : G.edgeFinset -> Nat => (#(finiteTreeMixedColorings (endsM G total) Finset.univ i j k l) : Real) * weight G beta J (ofEdgeFun G total)) ∧ finiteTreeMixedFourMass G beta J i j k l = ∑' total : G.edgeFinset -> Nat, (#(finiteTreeMixedColorings (endsM G total) Finset.univ i j k l) : Real) * weight G beta J (ofEdgeFun G total) := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedFourMass_eq_card_tsum G beta J hbeta hJ hij hkl

/--
[finiteTreeSeparatedFourMass_eq_card_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean)
-/
@[path]
private lemma finiteTreeSeparatedFourMass_eq_card_tsum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
  {y : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  Summable (fun total : G.edgeFinset -> Nat => (#(finiteTreeSeparatedBranchColorings (endsM G total) Finset.univ i j k l y) : Real) * weight G beta J (ofEdgeFun G total)) ∧ finiteTreeSeparatedFourMass G beta J i j k l y = ∑' total : G.edgeFinset -> Nat, (#(finiteTreeSeparatedBranchColorings (endsM G total) Finset.univ i j k l y) : Real) * weight G beta J (ofEdgeFun G total) := by
-- proof
  apply StatMech.FrontierA.finiteTreeSeparatedFourMass_eq_card_tsum G beta J hbeta hJ hij hkl y

/--
[finiteTreeMixedFourMass_le_sum_separated_of_cardBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean)
-/
@[path]
private lemma finiteTreeMixedFourMass_le_sum_separated_of_cardBound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hij : i ≠ j)
  (hkl : k ≠ l)
  (hcard : FiniteTreeColoringCardBound G i j k l) :
-- imply
  finiteTreeMixedFourMass G beta J i j k l <= ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedFourMass_le_sum_separated_of_cardBound G beta J hbeta hJ hij hkl hcard


-- created on 2026-10-23
