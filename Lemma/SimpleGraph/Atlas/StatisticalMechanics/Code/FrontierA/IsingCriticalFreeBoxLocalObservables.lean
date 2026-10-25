import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalFreeBoxLocalObservables.Part3
open Filter Finset MeasureTheory Topology StatMech StatMech.FrontierA


/--
[criticalFreeBoxLocalObservableExpectation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxLocalObservables.lean)
-/
@[path]
private lemma criticalFreeBoxLocalObservableExpectation_tendsto_eq
  {d : Nat}
  {A : Finset (Site d)}
-- given
  (hd : 2 < d)
  (f : ConfigSpace {x // x ∈ A} → Real) :
-- imply
  Tendsto (fun n ↦ criticalFreeBoxLocalObservableExpectation A f n) atTop (nhds (criticalFreeLocalObservableExpectation A f)) := by
-- proof
  apply StatMech.FrontierA.criticalFreeBoxLocalObservableExpectation_tendsto hd A f

/--
[finiteIsingWeightedSpinReal_compactFreeBoxWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxLocalObservables.lean)
-/
@[path]
private lemma finiteIsingWeightedSpinReal_compactFreeBoxWeight_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {n : Nat}
  {tau : ConfigSpace (sctBox d n)}
-- given
  (hA : (↑A : Set (Site d)) ⊆ box d n) :
-- imply
  finiteIsingWeightedSpinReal (compactFreeBoxWeight A a n) tau = compactWeightedSpin A a (criticalInfiniteLocalRestriction A (glue (minusField d) tau)) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedSpinReal_compactFreeBoxWeight A a n hA tau

/--
[finiteIsingWeightedRawMoment_eq_isingExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxLocalObservables.lean)
-/
@[path]
private lemma finiteIsingWeightedRawMoment_eq_isingExpectation_eq
  {d : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {a : V → Real}
  {order : Nat} :
-- imply
  finiteIsingWeightedRawMoment G beta a order = isingExpectation G beta 0 (fun sigma ↦ finiteIsingWeightedSpinReal a sigma ^ order) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedRawMoment_eq_isingExpectation G beta a order

/--
[criticalFreeBoxCompactWeightedMoment_eq_finiteRawMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxLocalObservables.lean)
-/
@[path]
private lemma criticalFreeBoxCompactWeightedMoment_eq_finiteRawMoment_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {n order : Nat}
-- given
  (hA : (↑A : Set (Site d)) ⊆ box d n) :
-- imply
  criticalFreeBoxCompactWeightedMoment A a n order = finiteIsingWeightedRawMoment (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (compactFreeBoxWeight A a n) order := by
-- proof
  apply StatMech.FrontierA.criticalFreeBoxCompactWeightedMoment_eq_finiteRawMoment A a n order hA

/--
[criticalFreeBoxCompactWeightedCumulant_eq_finiteCumulant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxLocalObservables.lean)
-/
@[path]
private lemma criticalFreeBoxCompactWeightedCumulant_eq_finiteCumulant_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {n order : Nat}
-- given
  (hA : (↑A : Set (Site d)) ⊆ box d n) :
-- imply
  criticalFreeBoxCompactWeightedCumulant A a n order = PhysicalIsing.finiteIsingWeightedCumulant (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (compactFreeBoxWeight A a n) order := by
-- proof
  apply StatMech.FrontierA.criticalFreeBoxCompactWeightedCumulant_eq_finiteCumulant A a n order hA

/--
[criticalFreeBoxCompactWeightedMoment_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxLocalObservables.lean)
-/
@[path]
private lemma criticalFreeBoxCompactWeightedMoment_tendsto_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {order : Nat}
-- given
  (hd : 2 < d) :
-- imply
  Tendsto (fun n ↦ criticalFreeBoxCompactWeightedMoment A a n order) atTop (nhds (criticalFreeLocalObservableExpectation A (fun sigma ↦ compactWeightedSpin A a sigma ^ order))) := by
-- proof
  apply StatMech.FrontierA.criticalFreeBoxCompactWeightedMoment_tendsto hd A a order

/--
[criticalFreeBoxCompactWeightedCumulant_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxLocalObservables.lean)
-/
@[path]
private lemma criticalFreeBoxCompactWeightedCumulant_tendsto_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {order : Nat}
-- given
  (hd : 2 < d) :
-- imply
  Tendsto (fun n ↦ criticalFreeBoxCompactWeightedCumulant A a n order) atTop (nhds (criticalFreeCompactWeightedCumulant A a order)) := by
-- proof
  apply StatMech.FrontierA.criticalFreeBoxCompactWeightedCumulant_tendsto hd A a order


-- created on 2026-10-23
