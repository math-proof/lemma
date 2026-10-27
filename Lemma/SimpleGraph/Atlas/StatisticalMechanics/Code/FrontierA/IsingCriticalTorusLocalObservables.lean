import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part4
open Filter Finset MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[khc_walshChar_eq_negOnePow_spinProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean)
-/
@[path]
private lemma khc_walshChar_eq_negOnePow_spinProd_eq
  {d : Nat}
  [Fintype V]
  [DecidableEq V]
  {B : Finset V}
  {sigma : ConfigSpace V} :
-- imply
  khc_walshChar B sigma = (-1 : Real) ^ B.card * spinProd B sigma := by
-- proof
  apply StatMech.FrontierA.khc_walshChar_eq_negOnePow_spinProd B sigma

/--
[criticalTorusLocalObservableExpectation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean)
-/
@[path]
private lemma criticalTorusLocalObservableExpectation_tendsto_eq
  {d : Nat}
  {A : Finset (Site d)}
-- given
  (hd : 2 < d)
  (f : ConfigSpace {x // x ∈ A} → Real) :
-- imply
  Tendsto (criticalTorusLocalObservableExpectation A f) atTop (nhds (criticalFreeLocalObservableExpectation A f)) := by
-- proof
  apply StatMech.FrontierA.criticalTorusLocalObservableExpectation_tendsto hd A f

/--
[criticalTorusLocalObservableExpectation_tendsto_varying](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean)
-/
@[path]
private lemma criticalTorusLocalObservableExpectation_tendsto_varying_eq
  {d : Nat}
  {A : Finset (Site d)}
-- given
  (hd : 2 < d)
  (f : Nat → ConfigSpace {x // x ∈ A} → Real)
  (limit : ConfigSpace {x // x ∈ A} → Real)
  (hf : ∀ sigma, Tendsto (fun n ↦ f n sigma) atTop (nhds (limit sigma))) :
-- imply
  Tendsto (fun n ↦ criticalTorusLocalObservableExpectation A (f n) n) atTop (nhds (criticalFreeLocalObservableExpectation A limit)) := by
-- proof
  apply StatMech.FrontierA.criticalTorusLocalObservableExpectation_tendsto_varying hd A f limit hf

/--
[criticalTorusCompactWeightedMoment_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean)
-/
@[path]
private lemma criticalTorusCompactWeightedMoment_tendsto_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {order : Nat}
-- given
  (hd : 2 < d) :
-- imply
  Tendsto (fun n ↦ criticalTorusLocalObservableExpectation A (fun sigma ↦ compactWeightedSpin A a sigma ^ order) n) atTop (nhds (criticalFreeLocalObservableExpectation A (fun sigma ↦ compactWeightedSpin A a sigma ^ order))) := by
-- proof
  apply StatMech.FrontierA.criticalTorusCompactWeightedMoment_tendsto hd A a order

/--
[finiteIsingWeightedSpinReal_compactTorusWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean)
-/
@[path]
private lemma finiteIsingWeightedSpinReal_compactTorusWeight_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {n : Nat}
  {sigma : ConfigSpace (IsingDyadicTorus d n)} :
-- imply
  finiteIsingWeightedSpinReal (compactTorusWeight A a n) sigma = compactWeightedSpin A a (criticalTorusLocalRestriction A n sigma) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedSpinReal_compactTorusWeight A a n sigma

/--
[finiteIsingWeightedRawMoment_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean)
-/
@[path]
private lemma finiteIsingWeightedRawMoment_eq_expJ_eq
  {d : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {a : V → Real}
  {order : Nat} :
-- imply
  finiteIsingWeightedRawMoment G beta a order = expJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) (fun sigma ↦ finiteIsingWeightedSpinReal a sigma ^ order) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedRawMoment_eq_expJ G beta a order

/--
[criticalTorusCompactWeightedMoment_eq_finiteRawMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean)
-/
@[path]
private lemma criticalTorusCompactWeightedMoment_eq_finiteRawMoment_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {n order : Nat} :
-- imply
  criticalTorusLocalObservableExpectation A (fun sigma ↦ compactWeightedSpin A a sigma ^ order) n = finiteIsingWeightedRawMoment (isingTorusGraph d n) (IsingFK.betaC (magnetization d)) (compactTorusWeight A a n) order := by
-- proof
  apply StatMech.FrontierA.criticalTorusCompactWeightedMoment_eq_finiteRawMoment A a n order

/--
[scalarCumulantsOfMoments_tendsto_of_moments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean)
-/
@[path]
private lemma scalarCumulantsOfMoments_tendsto_of_moments_eq
  {d : Nat}
  {moments : Nat → Nat → Real}
  {limitMoments : Nat → Real}
-- given
  (hmoments : ∀ order, Tendsto (fun n ↦ moments n order) atTop (nhds (limitMoments order))) :
-- imply
  ∀ order, Tendsto (fun n ↦ scalarCumulantsOfMoments (moments n) order) atTop (nhds (scalarCumulantsOfMoments limitMoments order)) := by
-- proof
  apply StatMech.FrontierA.scalarCumulantsOfMoments_tendsto_of_moments moments limitMoments hmoments

/--
[criticalTorusCompactWeightedCumulant_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean)
-/
@[path]
private lemma criticalTorusCompactWeightedCumulant_tendsto_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {order : Nat}
-- given
  (hd : 2 < d) :
-- imply
  Tendsto (fun n ↦ criticalTorusCompactWeightedCumulant A a n order) atTop (nhds (criticalFreeCompactWeightedCumulant A a order)) := by
-- proof
  apply StatMech.FrontierA.criticalTorusCompactWeightedCumulant_tendsto hd A a order

/--
[criticalTorusCompactWeightedCumulant_sub_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean)
-/
@[path]
private lemma criticalTorusCompactWeightedCumulant_sub_tendsto_zero_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {order : Nat}
-- given
  (hd : 2 < d) :
-- imply
  Tendsto (fun n ↦ criticalTorusCompactWeightedCumulant A a n order - criticalFreeCompactWeightedCumulant A a order) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.criticalTorusCompactWeightedCumulant_sub_tendsto_zero hd A a order


-- created on 2026-10-23
