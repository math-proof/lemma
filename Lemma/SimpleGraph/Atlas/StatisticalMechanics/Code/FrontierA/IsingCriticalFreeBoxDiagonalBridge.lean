import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingCriticalFreeBoxDiagonalBridge
open Filter Finset MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[finiteSupport_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxDiagonalBridge.lean)
-/
@[path]
private lemma finiteSupport_subset_box_eq
  {d : Nat}
  {A : Finset (Site d)} :
-- imply
  (↑A : Set (Site d)) ⊆ box d (finiteSupportBoxRadius A) := by
-- proof
  apply StatMech.FrontierA.finiteSupport_subset_box A

/--
[exists_criticalFreeBoxGrowingCompactCumulant_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxDiagonalBridge.lean)
-/
@[path]
private lemma exists_criticalFreeBoxGrowingCompactCumulant_diagonal_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
-- given
  (hd : 2 < d) :
-- imply
  ∃ boxScale : Nat → Nat, Tendsto boxScale atTop atTop ∧ (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧ ∀ n order, order ≤ n → := by
-- proof
  apply StatMech.FrontierA.exists_criticalFreeBoxGrowingCompactCumulant_diagonal hd A a

/--
[criticalFreeCompactWeightedCumulant_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxDiagonalBridge.lean)
-/
@[path]
private lemma criticalFreeCompactWeightedCumulant_scale_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {c : Real}
  {order : Nat} :
-- imply
  criticalFreeCompactWeightedCumulant A (fun x ↦ c * a x) order = c ^ order * criticalFreeCompactWeightedCumulant A a order := by
-- proof
  apply StatMech.FrontierA.criticalFreeCompactWeightedCumulant_scale A a c order

/--
[criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero_along](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxDiagonalBridge.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero_along_eq
  {d : Nat}
  {d : Nat}
  {boxScale : Nat → Nat}
  {a : (n : Nat) → sctBox d (boxScale n) → Real}
-- given
  (hd : 4 < d)
  (hboxScale : Tendsto boxScale atTop atTop)
  (ha0 : ∀ n x, 0 ≤ a n x)
  (ha1 : ∀ n x, a n x ≤ 1) :
-- imply
  Tendsto (fun n ↦ PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant d (boxScale n) (by omega) (a n) 4) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero_along d hd boxScale hboxScale a ha0 ha1

/--
[exists_criticalFreeGrowingCanonicalScaledFourthCumulant_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxDiagonalBridge.lean)
-/
@[path]
private lemma exists_criticalFreeGrowingCanonicalScaledFourthCumulant_tendsto_zero_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
-- given
  (hd : 4 < d)
  (ha0 : ∀ n x, 0 ≤ a n x)
  (ha1 : ∀ n x, a n x ≤ 1) :
-- imply
  ∃ boxScale : Nat → Nat, Tendsto boxScale atTop atTop ∧ (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧ Tendsto (fun n ↦ criticalFreeCompactWeightedCumulant (A n) (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale d (boxScale n) (by omega) * a n x) 4) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.exists_criticalFreeGrowingCanonicalScaledFourthCumulant_tendsto_zero hd A a ha0 ha1

/--
[exists_criticalTorusGrowingCanonicalScaledFourthCumulant_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxDiagonalBridge.lean)
-/
@[path]
private lemma exists_criticalTorusGrowingCanonicalScaledFourthCumulant_tendsto_zero_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
-- given
  (hd : 4 < d)
  (ha0 : ∀ n x, 0 ≤ a n x)
  (ha1 : ∀ n x, a n x ≤ 1) :
-- imply
  ∃ boxScale torusScale : Nat → Nat, Tendsto boxScale atTop atTop ∧ Tendsto torusScale atTop atTop ∧ (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧ Tendsto (fun n ↦ criticalTorusCompactWeightedCumulant (A n) (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale d (boxScale n) (by omega) * a n x) (torusScale n) 4) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.exists_criticalTorusGrowingCanonicalScaledFourthCumulant_tendsto_zero hd A a ha0 ha1

/--
[exists_criticalTorusGrowingCanonicalScaledCumulantLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxDiagonalBridge.lean)
-/
@[path]
private lemma exists_criticalTorusGrowingCanonicalScaledCumulantLimits_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
-- given
  (hd : 4 < d)
  (ha0 : ∀ n x, 0 ≤ a n x)
  (ha1 : ∀ n x, a n x ≤ 1) :
-- imply
  ∃ boxScale torusScale : Nat → Nat, Tendsto boxScale atTop atTop ∧ Tendsto torusScale atTop atTop ∧ (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧ ∀ variance : Real, Tendsto (fun n ↦ criticalTorusCompactWeightedCumulant (A n) (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale d (boxScale n) (by omega) * a n x) (torusScale n) 2) atTop (nhds variance) → ∀ order, Tendsto (fun n ↦ criticalTorusCompactWeightedCumulant (A n) (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale d (boxScale n) (by omega) * a n x) (torusScale n) order) atTop (nhds (scalarGaussianCumulant variance order)) := by
-- proof
  apply StatMech.FrontierA.exists_criticalTorusGrowingCanonicalScaledCumulantLimits hd A a ha0 ha1


-- created on 2026-10-23
