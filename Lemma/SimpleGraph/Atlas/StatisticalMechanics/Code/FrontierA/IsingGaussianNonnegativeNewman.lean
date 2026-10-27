import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNonnegativeNewman
open Filter Finset Topology StatMech StatMech.FrontierA


/--
[finiteIsingWeighted_physical_newmanFourthCumulantControl_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNonnegativeNewman.lean)
-/
@[path]
private lemma finiteIsingWeighted_physical_newmanFourthCumulantControl_nonnegative_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {a : V → Real}
-- given
  (hbeta : 0 ≤ beta)
  (ha : ∀ v, 0 ≤ a v) :
-- imply
  NewmanFourthCumulantControl (fun _ order ↦ PhysicalIsing.finiteIsingWeightedCumulant G beta a order) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeighted_physical_newmanFourthCumulantControl_nonnegative G beta hbeta a ha

/--
[criticalTorusGrowingCompactWeighted_newmanFourthCumulantControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNonnegativeNewman.lean)
-/
@[path]
private lemma criticalTorusGrowingCompactWeighted_newmanFourthCumulantControl_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
  {torusScale : Nat → Nat}
-- given
  (hd : 2 ≤ d)
  (ha : ∀ n x, 0 ≤ a n x) :
-- imply
  NewmanFourthCumulantControl (fun n order ↦ criticalTorusCompactWeightedCumulant (A n) (a n) (torusScale n) order) := by
-- proof
  apply StatMech.FrontierA.criticalTorusGrowingCompactWeighted_newmanFourthCumulantControl hd A a torusScale ha


-- created on 2026-10-23
