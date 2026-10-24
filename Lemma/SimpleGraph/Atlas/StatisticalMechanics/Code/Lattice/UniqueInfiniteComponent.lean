import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent
open Set SimpleGraph StatMech StatMech.Lattice


/--
[mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma mem_exterior_eq
  {d : ℕ}
  {d R : ℕ}
  {x : Site d} :
-- imply
  x ∈ exterior d R ↔ ∃ i, R < (x i).natAbs := by
-- proof
  apply StatMech.Lattice.mem_exterior

/--
[exterior_eq_compl_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma exterior_eq_compl_box_eq
  {d : ℕ}
  {d R : ℕ} :
-- imply
  exterior d R = (box d R)ᶜ := by
-- proof
  apply StatMech.Lattice.exterior_eq_compl_box d R

/--
[segment_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma segment_up_eq
  {d : ℕ}
  {S : Set (Site d)}
  {j : Fin d}
  {p : Site d}
  {c : ℤ}
-- given
  (hpc : p j ≤ c)
  (hp : p ∈ S)
  (hc : Function.update p j c ∈ S)
  (hseg : ∀ z : ℤ, (p j ≤ z ∧ z ≤ c) → Function.update p j z ∈ S) :
-- imply
  ((hypercubicLattice d).induce S).Reachable ⟨p, hp⟩ ⟨Function.update p j c, hc⟩ := by
-- proof
  apply StatMech.Lattice.segment_up S j p c hpc hp hc hseg

/--
[segment_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma segment_gen_eq
  {d : ℕ}
  {S : Set (Site d)}
  {j : Fin d}
  {p : Site d}
  {c : ℤ}
-- given
  (hp : p ∈ S)
  (hc : Function.update p j c ∈ S)
  (hseg : ∀ z : ℤ, (min (p j) c ≤ z ∧ z ≤ max (p j) c) → Function.update p j z ∈ S) :
-- imply
  ((hypercubicLattice d).induce S).Reachable ⟨p, hp⟩ ⟨Function.update p j c, hc⟩ := by
-- proof
  apply StatMech.Lattice.segment_gen S j p c hp hc hseg

/--
[setOn_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma setOn_empty_eq
  {d : ℕ}
  {p : Site d}
  {v : ℤ} :
-- imply
  setOn p ∅ v = p := by
-- proof
  apply StatMech.Lattice.setOn_empty p v

/--
[setOn_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma setOn_insert_eq
  {d : ℕ}
  {p : Site d}
  {T : Finset (Fin d)}
  {j : Fin d}
  {v : ℤ}
-- given
  (hj : j ∉ T) :
-- imply
  setOn p (insert j T) v = Function.update (setOn p T v) j v := by
-- proof
  apply StatMech.Lattice.setOn_insert p T j v hj

/--
[setOn_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma setOn_notMem_eq
  {d : ℕ}
  {p : Site d}
  {T : Finset (Fin d)}
  {v : ℤ}
  {i0 : Fin d}
-- given
  (h : i0 ∉ T) :
-- imply
  setOn p T v i0 = p i0 := by
-- proof
  apply StatMech.Lattice.setOn_notMem p T v h

/--
[exterior_reachable_setOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma exterior_reachable_setOn_eq
  {d : ℕ}
  {R : ℕ}
  {p : Site d}
  {i0 : Fin d}
  {T : Finset (Fin d)}
-- given
  (hi0 : R < (p i0).natAbs)
  (hT : i0 ∉ T)
  (hpext : p ∈ exterior d R)
  (htgt : setOn p T ((R : ℤ) + 1) ∈ exterior d R) :
-- imply
  ((hypercubicLattice d).induce (exterior d R)).Reachable ⟨p, hpext⟩ ⟨setOn p T ((R : ℤ) + 1), htgt⟩ := by
-- proof
  apply StatMech.Lattice.exterior_reachable_setOn R p i0 hi0 T hT hpext htgt

/--
[beacon_natAbs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma beacon_natAbs_eq
  {d : ℕ}
  {R : ℕ}
  {k : Fin d} :
-- imply
  ((beacon d R) k).natAbs = R + 1 := by
-- proof
  apply StatMech.Lattice.beacon_natAbs R k

/--
[beacon_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma beacon_mem_exterior_eq
  {d : ℕ}
  {R : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  beacon d R ∈ exterior d R := by
-- proof
  apply StatMech.Lattice.beacon_mem_exterior R hd

/--
[exterior_reachable_beacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma exterior_reachable_beacon_eq
  {d : ℕ}
  {R : ℕ}
  {p : Site d}
-- given
  (hd : 2 ≤ d)
  (hp : p ∈ exterior d R) :
-- imply
  ((hypercubicLattice d).induce (exterior d R)).Reachable ⟨p, hp⟩ ⟨beacon d R, beacon_mem_exterior R (by omega)⟩ := by
-- proof
  apply StatMech.Lattice.exterior_reachable_beacon R hd p hp

/--
[box_exterior_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma box_exterior_connected_eq
  {d : ℕ}
  {R : ℕ}
  {x y : Site d}
-- given
  (hd : 2 ≤ d)
  (hx : x ∈ exterior d R)
  (hy : y ∈ exterior d R) :
-- imply
  ((hypercubicLattice d).induce (exterior d R)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Lattice.box_exterior_connected R hd x y hx hy

/--
[exterior_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma exterior_infinite_eq
  {d : ℕ}
  {R : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  (exterior d R).Infinite := by
-- proof
  apply StatMech.Lattice.exterior_infinite R hd

/--
[finite_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma finite_subset_box_eq
  {d : ℕ}
  {F : Set (Site d)}
-- given
  (hF : F.Finite) :
-- imply
  ∃ R : ℕ, F ⊆ box d R := by
-- proof
  apply StatMech.Lattice.finite_subset_box F hF

/--
[exterior_subset_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma exterior_subset_compl_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
-- given
  (hF : F ⊆ box d R) :
-- imply
  exterior d R ⊆ Fᶜ := by
-- proof
  apply StatMech.Lattice.exterior_subset_compl F R hF

/--
[exterior_reachable_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma exterior_reachable_compl_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
  {x y : Site d}
-- given
  (hd : 2 ≤ d)
  (hsub : exterior d R ⊆ Fᶜ)
  (hx : x ∈ exterior d R)
  (hy : y ∈ exterior d R) :
-- imply
  ((hypercubicLattice d).induce Fᶜ).Reachable ⟨x, hsub hx⟩ ⟨y, hsub hy⟩ := by
-- proof
  apply StatMech.Lattice.exterior_reachable_compl F R hd hsub x y hx hy

/--
[unique_infinite_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean)
-/
@[path]
private lemma unique_infinite_component_eq
  {d : ℕ}
  {F : Set (Site d)}
-- given
  (hd : 2 ≤ d)
  (hF : F.Finite) :
-- imply
  ∃! C : ((hypercubicLattice d).induce Fᶜ).ConnectedComponent, C.supp.Infinite := by
-- proof
  apply StatMech.Lattice.unique_infinite_component hd F hF


-- created on 2026-10-23
