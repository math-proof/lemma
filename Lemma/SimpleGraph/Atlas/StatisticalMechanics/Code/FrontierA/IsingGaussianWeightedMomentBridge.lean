import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedMomentBridge.Part2
open Finset StatMech StatMech.FrontierA


/--
[ofReal_finiteIsingWeightedSpinReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma ofReal_finiteIsingWeightedSpinReal_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
-- given
  (a : V -> Real) :
-- imply
  (finiteIsingWeightedSpinReal a s : Complex) = finiteIsingWeightedSpin a s := by
-- proof
  apply StatMech.FrontierA.ofReal_finiteIsingWeightedSpinReal a s

/--
[finiteIsingWeightedMomentGeneratingFunction_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma finiteIsingWeightedMomentGeneratingFunction_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
-- given
  (a : V -> Real) :
-- imply
  finiteIsingWeightedMomentGeneratingFunction G beta a 0 = 1 := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedMomentGeneratingFunction_zero beta a

/--
[finiteIsingWeightedMomentGeneratingFunction_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma finiteIsingWeightedMomentGeneratingFunction_neg_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {z : Complex}
-- given
  (a : V -> Real) :
-- imply
  finiteIsingWeightedMomentGeneratingFunction G beta a (-z) = finiteIsingWeightedMomentGeneratingFunction G beta a z := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedMomentGeneratingFunction_neg beta a z

/--
[finiteIsingWeightedMomentGeneratingFunction_analyticOnNhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma finiteIsingWeightedMomentGeneratingFunction_analyticOnNhd_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
-- given
  (a : V -> Real) :
-- imply
  AnalyticOnNhd Complex (finiteIsingWeightedMomentGeneratingFunction G beta a) Set.univ := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedMomentGeneratingFunction_analyticOnNhd beta a

/--
[finiteIsingWeightedMomentGeneratingFunction_ne_zero_of_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma finiteIsingWeightedMomentGeneratingFunction_ne_zero_of_re_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {z : Complex}
-- given
  (hbeta : 0 <= beta)
  (a : V -> Real)
  (ha : forall v, 0 < a v)
  (hz : z.re ≠ 0) :
-- imply
  finiteIsingWeightedMomentGeneratingFunction G beta a z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedMomentGeneratingFunction_ne_zero_of_re_ne_zero beta hbeta a ha z hz

/--
[iteratedDeriv_finiteIsingWeightedFieldPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma iteratedDeriv_finiteIsingWeightedFieldPartition_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
  {z : Complex}
-- given
  (a : V -> Real) :
-- imply
  iteratedDeriv order (finiteIsingWeightedFieldPartition G beta a) z = ∑ s : ConfigSpace V, (zeroFieldInteractionWeight G beta s : Complex) * finiteIsingWeightedSpin a s ^ order * Complex.exp (finiteIsingWeightedSpin a s * z) := by
-- proof
  apply StatMech.FrontierA.iteratedDeriv_finiteIsingWeightedFieldPartition beta a order z

/--
[iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
-- given
  (a : V -> Real) :
-- imply
  iteratedDeriv order (finiteIsingWeightedMomentGeneratingFunction G beta a) 0 = (∑ s : ConfigSpace V, (zeroFieldInteractionWeight G beta s : Complex) * finiteIsingWeightedSpin a s ^ order) / finiteIsingWeightedFieldPartition G beta a 0 := by
-- proof
  apply StatMech.FrontierA.iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero beta a order

/--
[iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq_rawMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq_rawMoment_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
-- given
  (a : V -> Real) :
-- imply
  iteratedDeriv order (finiteIsingWeightedMomentGeneratingFunction G beta a) 0 = (finiteIsingWeightedRawMoment G beta a order : Complex) := by
-- proof
  apply StatMech.FrontierA.iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq_rawMoment beta a order

/--
[finiteIsingWeightedRawMoment_two_eq_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma finiteIsingWeightedRawMoment_two_eq_parity_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
-- given
  (a : V -> Real) :
-- imply
  finiteIsingWeightedRawMoment G beta a 2 = finiteWeightedParitySecondMoment G beta (fun _ => 1) a := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedRawMoment_two_eq_parity beta a

/--
[finiteIsingWeightedRawMoment_four_eq_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma finiteIsingWeightedRawMoment_four_eq_parity_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
-- given
  (a : V -> Real) :
-- imply
  finiteIsingWeightedRawMoment G beta a 4 = finiteWeightedParityFourthMoment G beta (fun _ => 1) a := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedRawMoment_four_eq_parity beta a

/--
[scalarFourthCumulant_finiteIsingWeightedRawMoment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean)
-/
@[path]
private lemma scalarFourthCumulant_finiteIsingWeightedRawMoment_eq_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
-- given
  (a : V -> Real) :
-- imply
  scalarFourthCumulant (finiteIsingWeightedRawMoment G beta a 4) (finiteIsingWeightedRawMoment G beta a 2) = finiteWeightedParityFourthCumulant G beta (fun _ => 1) a := by
-- proof
  apply StatMech.FrontierA.scalarFourthCumulant_finiteIsingWeightedRawMoment_eq beta a


-- created on 2026-10-23
