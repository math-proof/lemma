import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedLeeYang
open Finset StatMech StatMech.FrontierA


/--
[leeYangWeightedDiagonal_norm_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean)
-/
@[path]
private lemma leeYangWeightedDiagonal_norm_lt_eq
  [Fintype V]
  [DecidableEq V]
  {z : Complex}
-- given
  (a : V -> Real)
  (ha : forall v, 0 < a v)
  (hz : 0 < z.re) :
-- imply
  forall k, ‖leeYangWeightedDiagonal G a z k‖ < 1 := by
-- proof
  apply StatMech.FrontierA.leeYangWeightedDiagonal_norm_lt a ha hz

/--
[leeYangContractedProduct_weighted_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean)
-/
@[path]
private lemma leeYangContractedProduct_weighted_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {z : Complex}
-- given
  (hbeta : 0 <= beta)
  (a : V -> Real)
  (ha : forall v, 0 < a v)
  (hz : 0 < z.re) :
-- imply
  leeYangContractedProduct G beta (leeYangWeightedDiagonal G a z) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.leeYangContractedProduct_weighted_ne_zero hbeta a ha hz

/--
[leeYangMonomial_anchorSupport_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean)
-/
@[path]
private lemma leeYangMonomial_anchorSupport_weighted_eq
  [Fintype V]
  [DecidableEq V]
  {z : Complex}
-- given
  (sigma : V -> Bool)
  (a : V -> Real) :
-- imply
  leeYangMonomial (leeYangAnchorSupport G sigma) (leeYangWeightedDiagonal G a z) = ∏ v : V, if sigma v = true then Complex.exp (-2 * (a v : Complex) * z) else 1 := by
-- proof
  apply StatMech.FrontierA.leeYangMonomial_anchorSupport_weighted sigma a z

/--
[exp_weightedSpin_eq_total_mul_monomial_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean)
-/
@[path]
private lemma exp_weightedSpin_eq_total_mul_monomial_flip_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {z : Complex}
-- given
  (a : V -> Real) :
-- imply
  Complex.exp (z * ∑ v : V, (a v : Complex)) * leeYangMonomial (leeYangAnchorSupport G (leeYangFlip s)) (leeYangWeightedDiagonal G a z) = Complex.exp (z * ∑ v : V, (a v : Complex) * spin s v) := by
-- proof
  apply StatMech.FrontierA.exp_weightedSpin_eq_total_mul_monomial_flip s a z

/--
[leeYangContractedProduct_weighted_eq_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean)
-/
@[path]
private lemma leeYangContractedProduct_weighted_eq_partition_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {z : Complex}
-- given
  (a : V -> Real) :
-- imply
  (Real.exp (beta * G.edgeFinset.card) : Complex) * Complex.exp (z * ∑ v : V, (a v : Complex)) * leeYangContractedProduct G beta (leeYangWeightedDiagonal G a z) = finiteIsingWeightedFieldPartition G beta a z := by
-- proof
  apply StatMech.FrontierA.leeYangContractedProduct_weighted_eq_partition beta a z

/--
[finiteIsingWeightedFieldPartition_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean)
-/
@[path]
private lemma finiteIsingWeightedFieldPartition_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {z : Complex}
-- given
  (hbeta : 0 <= beta)
  (a : V -> Real)
  (ha : forall v, 0 < a v)
  (hz : 0 < z.re) :
-- imply
  finiteIsingWeightedFieldPartition G beta a z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedFieldPartition_ne_zero hbeta a ha hz

/--
[finiteIsingWeightedFieldPartition_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean)
-/
@[path]
private lemma finiteIsingWeightedFieldPartition_neg_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {z : Complex}
-- given
  (a : V -> Real) :
-- imply
  finiteIsingWeightedFieldPartition G beta a (-z) = finiteIsingWeightedFieldPartition G beta a z := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedFieldPartition_neg beta a z

/--
[finiteIsingWeightedFieldPartition_ne_zero_of_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean)
-/
@[path]
private lemma finiteIsingWeightedFieldPartition_ne_zero_of_re_ne_zero_eq
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
  finiteIsingWeightedFieldPartition G beta a z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedFieldPartition_ne_zero_of_re_ne_zero hbeta a ha hz


-- created on 2026-10-23
