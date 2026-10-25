import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorVanishing.Part2
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[twoArmDisconnectedTraceEvent_real_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorVanishing.lean)
-/
@[path]
private lemma twoArmDisconnectedTraceEvent_real_tendsto_zero_eq
  {d : Nat}
  {mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d}
-- given
  (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0) :
-- imply
  Tendsto (fun m => (mu : Measure _).real (twoArmDisconnectedTraceEvent m x y)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierB.twoArmDisconnectedTraceEvent_real_tendsto_zero mu hunique x y

/--
[twoOddCrossClustersEvent_subset_twoArmUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorVanishing.lean)
-/
@[path]
private lemma twoOddCrossClustersEvent_subset_twoArmUnion_eq
  {d : Nat}
  {m : Nat}
  {A B : Finset (Site d)}
-- given
  (hm : 1 ≤ m)
  (hA : (A : Set (Site d)) ⊆ box d (m - 1))
  (hB : (B : Set (Site d)) ⊆ (box d (m - 1))ᶜ) :
-- imply
  twoOddCrossClustersEvent (hypercubicLattice d) A B ⊆ ⋃ x ∈ A, ⋃ y ∈ A, twoArmDisconnectedTraceEvent m x y := by
-- proof
  apply StatMech.FrontierB.twoOddCrossClustersEvent_subset_twoArmUnion m hm A B hA hB

/--
[inverseAxisTranslateFinset_eventually_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorVanishing.lean)
-/
@[path]
private lemma inverseAxisTranslateFinset_eventually_outside_box_eq
  {d : Nat}
  {B : Finset (Site d)}
  {m : Nat}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∀ᶠ n in atTop, (inverseAxisTranslateFinset hd n B : Set (Site d)) ⊆ (box d m)ᶜ := by
-- proof
  apply StatMech.FrontierB.inverseAxisTranslateFinset_eventually_outside_box hd B m

/--
[twoOddCrossClusters_axisTranslate_real_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorVanishing.lean)
-/
@[path]
private lemma twoOddCrossClusters_axisTranslate_real_tendsto_zero_eq
  {d : Nat}
  {mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {A B : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0) :
-- imply
  Tendsto (fun n => (mu : Measure _).real (twoOddCrossClustersEvent (hypercubicLattice d) A (inverseAxisTranslateFinset hd n B))) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierB.twoOddCrossClusters_axisTranslate_real_tendsto_zero hd mu hunique A B


-- created on 2026-10-23
