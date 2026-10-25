import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalPolarization.Part4
open Filter Finset Polynomial Topology StatMech StatMech.FrontierA StatMech.FrontierA.PhysicalIsing


/--
[finiteIsingWeightedRawMomentLinePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean)
-/
@[path]
private lemma finiteIsingWeightedRawMomentLinePolynomial_eval_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
  {r : Real}
-- given
  (positive direction : V -> Real) :
-- imply
  (finiteIsingWeightedRawMomentLinePolynomial G beta positive direction order).eval r = finiteIsingWeightedRawMoment G beta (positive + r • direction) order := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedRawMomentLinePolynomial_eval beta positive direction order r

/--
[finiteIsingWeightedRawMomentLinePolynomial_natDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean)
-/
@[path]
private lemma finiteIsingWeightedRawMomentLinePolynomial_natDegree_le_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
-- given
  (positive direction : V -> Real) :
-- imply
  (finiteIsingWeightedRawMomentLinePolynomial G beta positive direction order).natDegree <= order := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedRawMomentLinePolynomial_natDegree_le beta positive direction order

/--
[scalarCumulantLinePolynomial_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean)
-/
@[path]
private lemma scalarCumulantLinePolynomial_succ_eq
  [Fintype V]
  [DecidableEq V]
  {n : Nat}
-- given
  (moments : Nat -> Real[X]) :
-- imply
  scalarCumulantLinePolynomial moments (n + 1) = moments (n + 1) - ∑ k : Fin n, C (n.choose k : Real) * scalarCumulantLinePolynomial moments (k + 1) * moments (n - k) := by
-- proof
  apply StatMech.FrontierA.scalarCumulantLinePolynomial_succ moments n

/--
[scalarCumulantLinePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean)
-/
@[path]
private lemma scalarCumulantLinePolynomial_eval_eq
  [Fintype V]
  [DecidableEq V]
  {r : Real}
-- given
  (moments : Nat -> Real[X]) :
-- imply
  forall order, (scalarCumulantLinePolynomial moments order).eval r = scalarCumulantsOfMoments (fun m => (moments m).eval r) order := by
-- proof
  apply StatMech.FrontierA.scalarCumulantLinePolynomial_eval moments r

/--
[scalarCumulantLinePolynomial_natDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean)
-/
@[path]
private lemma scalarCumulantLinePolynomial_natDegree_le_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (moments : Nat -> Real[X])
  (hmoments : forall order, (moments order).natDegree <= order) :
-- imply
  forall order, (scalarCumulantLinePolynomial moments order).natDegree <= order := by
-- proof
  apply StatMech.FrontierA.scalarCumulantLinePolynomial_natDegree_le moments hmoments

/--
[finiteIsingWeightedCumulantLinePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean)
-/
@[path]
private lemma finiteIsingWeightedCumulantLinePolynomial_eval_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
  {r : Real}
-- given
  (positive direction : V -> Real) :
-- imply
  (finiteIsingWeightedCumulantLinePolynomial G beta positive direction order).eval r = PhysicalIsing.finiteIsingWeightedCumulant G beta (positive + r • direction) order := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedCumulantLinePolynomial_eval beta positive direction order r

/--
[finiteIsingWeightedCumulantLinePolynomial_degree_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean)
-/
@[path]
private lemma finiteIsingWeightedCumulantLinePolynomial_degree_lt_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
-- given
  (positive direction : V -> Real) :
-- imply
  (finiteIsingWeightedCumulantLinePolynomial G beta positive direction order).degree < (order + 1 : Nat) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedCumulantLinePolynomial_degree_lt beta positive direction order

/--
[criticalFiniteBoxWeightedScaledCumulantLinePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedScaledCumulantLinePolynomial_eval_eq
  [Fintype V]
  [DecidableEq V]
  {d n : Nat}
  {order : Nat}
  {r : Real}
-- given
  (hd : 2 <= d)
  (positive direction : sctBox d n -> Real) :
-- imply
  (criticalFiniteBoxWeightedScaledCumulantLinePolynomial d n hd positive direction order).eval r = criticalFiniteBoxWeightedScaledCumulant d n hd (positive + r • direction) order := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.criticalFiniteBoxWeightedScaledCumulantLinePolynomial_eval d n hd positive direction order r

/--
[criticalFiniteBoxWeightedScaledCumulantLinePolynomial_degree_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedScaledCumulantLinePolynomial_degree_lt_eq
  [Fintype V]
  [DecidableEq V]
  {d n : Nat}
  {order : Nat}
-- given
  (hd : 2 <= d)
  (positive direction : sctBox d n -> Real) :
-- imply
  (criticalFiniteBoxWeightedScaledCumulantLinePolynomial d n hd positive direction order).degree < (order + 1 : Nat) := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.criticalFiniteBoxWeightedScaledCumulantLinePolynomial_degree_lt d n hd positive direction order

/--
[criticalFiniteBoxWeightedScaledCumulant_tendsto_zero_of_nonnegative_line](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedScaledCumulant_tendsto_zero_of_nonnegative_line_eq
  [Fintype V]
  [DecidableEq V]
  {d order : Nat}
-- given
  (hd : 2 <= d)
  (positive negative signed : (n : Nat) -> sctBox d n -> Real)
  (hsigned : forall n, signed n = positive n - negative n)
  (hnodes : forall i : Fin (order + 1), Tendsto (fun n => criticalFiniteBoxWeightedScaledCumulant d n hd (positive n + (((i : Nat) : Real) • negative n)) order) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => criticalFiniteBoxWeightedScaledCumulant d n hd (signed n) order) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant_tendsto_zero_of_nonnegative_line d order hd positive negative signed hsigned hnodes


-- created on 2026-10-23
