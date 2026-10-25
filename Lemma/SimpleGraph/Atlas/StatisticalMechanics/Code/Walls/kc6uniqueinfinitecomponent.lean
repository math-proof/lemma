import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc6uniqueinfinitecomponent
open Set SimpleGraph StatMech StatMech.Walls


/--
[kc6_beacon_mem_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6uniqueinfinitecomponent.lean)
-/
@[path]
private lemma kc6_beacon_mem_compl_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
-- given
  (hd : 1 ≤ d)
  (hF : F ⊆ box d R) :
-- imply
  beacon d R ∈ Fᶜ := by
-- proof
  apply StatMech.Walls.kc6_beacon_mem_compl hd F R hF

/--
[kc6_beacon_component_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6uniqueinfinitecomponent.lean)
-/
@[path]
private lemma kc6_beacon_component_infinite_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
-- given
  (hd : 2 ≤ d)
  (hF : F ⊆ box d R) :
-- imply
  (((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩).supp.Infinite := by
-- proof
  apply StatMech.Walls.kc6_beacon_component_infinite hd F R hF

/--
[kc6_unique_infinite_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6uniqueinfinitecomponent.lean)
-/
@[path]
private lemma kc6_unique_infinite_component_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
-- given
  (hd : 2 ≤ d)
  (hF : F ⊆ box d R) :
-- imply
  ∃! C : ((hypercubicLattice d).induce Fᶜ).ConnectedComponent, C.supp.Infinite ∧ C = ((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩ := by
-- proof
  apply StatMech.Walls.kc6_unique_infinite_component hd F R hF

/--
[kc6_infinite_iff_eq_beacon_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6uniqueinfinitecomponent.lean)
-/
@[path]
private lemma kc6_infinite_iff_eq_beacon_component_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
  {C : ((hypercubicLattice d).induce Fᶜ).ConnectedComponent}
-- given
  (hd : 2 ≤ d)
  (hFfin : F.Finite)
  (hF : F ⊆ box d R) :
-- imply
  C.supp.Infinite ↔ C = ((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩ := by
-- proof
  apply StatMech.Walls.kc6_infinite_iff_eq_beacon_component hd F hFfin R hF C

/--
[kc6_infinite_iff_reachable_beacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6uniqueinfinitecomponent.lean)
-/
@[path]
private lemma kc6_infinite_iff_reachable_beacon_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
  {z : Site d}
-- given
  (hd : 2 ≤ d)
  (hFfin : F.Finite)
  (hF : F ⊆ box d R)
  (hzmem : z ∈ Fᶜ) :
-- imply
  (((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite ↔ ((hypercubicLattice d).induce Fᶜ).Reachable ⟨z, hzmem⟩ ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩ := by
-- proof
  apply StatMech.Walls.kc6_infinite_iff_reachable_beacon hd F hFfin R hF hzmem

/--
[kc6_exterior_eq_beacon_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6uniqueinfinitecomponent.lean)
-/
@[path]
private lemma kc6_exterior_eq_beacon_component_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
  {z : Site d}
-- given
  (hd : 2 ≤ d)
  (hF : F ⊆ box d R)
  (hz : z ∈ exterior d R) :
-- imply
  ∃ hzmem : z ∈ Fᶜ, ((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨z, hzmem⟩ = ((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩ := by
-- proof
  apply StatMech.Walls.kc6_exterior_eq_beacon_component hd F R hF hz

/--
[kc6_exterior_component_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6uniqueinfinitecomponent.lean)
-/
@[path]
private lemma kc6_exterior_component_infinite_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
  {z : Site d}
-- given
  (hd : 2 ≤ d)
  (hFfin : F.Finite)
  (hF : F ⊆ box d R)
  (hz : z ∈ exterior d R) :
-- imply
  ∃ hzmem : z ∈ Fᶜ, (((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite := by
-- proof
  apply StatMech.Walls.kc6_exterior_component_infinite hd F hFfin R hF hz


-- created on 2026-10-23
