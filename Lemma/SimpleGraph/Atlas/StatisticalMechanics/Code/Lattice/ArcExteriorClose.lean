import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ArcExteriorClose.Part3
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[arcxc_exterior_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_exterior_offSupport_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {z : Site 2}
-- given
  (hB : B ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  z ∉ B := by
-- proof
  apply StatMech.Lattice.arcxc_exterior_offSupport hB hz

/--
[arcxc_exterior_adj_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_exterior_adj_offSupport_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hB : B ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R)
  (hadj : (hypercubicLattice 2).Adj x y) :
-- imply
  (ffc_offSupportLattice B).Adj x y := by
-- proof
  apply StatMech.Lattice.arcxc_exterior_adj_offSupport hB hx hy hadj

/--
[arcxc_exterior_reachable_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_exterior_reachable_offSupport_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hB : B ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  (ffc_offSupportLattice B).Reachable x y := by
-- proof
  apply StatMech.Lattice.arcxc_exterior_reachable_offSupport hB hx hy

/--
[arcxc_exterior_walk_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_exterior_walk_offSupport_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hB : B ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B := by
-- proof
  apply StatMech.Lattice.arcxc_exterior_walk_offSupport hB hx hy

/--
[arcxc_connected_of_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_connected_of_reachesExterior_eq
  {B : Set (Site 2)}
  {R : ℕ}
-- given
  (h : arcxc_ReachesExterior B R) :
-- imply
  arcns_OffSupportConnected B := by
-- proof
  apply StatMech.Lattice.arcxc_connected_of_reachesExterior h

/--
[arcxc_mem_exterior_of_col_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_mem_exterior_of_col_high_eq
  {R : ℕ}
  {z : Site 2}
-- given
  (hz : (R : ℤ) + 1 ≤ z 0) :
-- imply
  z ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.arcxc_mem_exterior_of_col_high R hz

/--
[arcxc_mem_exterior_of_row_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_mem_exterior_of_row_high_eq
  {R : ℕ}
  {z : Site 2}
-- given
  (hz : (R : ℤ) + 1 ≤ z 1) :
-- imply
  z ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.arcxc_mem_exterior_of_row_high R hz

/--
[arcxc_reachesExterior_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_reachesExterior_of_walk_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {z e : Site 2}
  {p : (hypercubicLattice 2).Walk z e}
-- given
  (heExt : e ∈ exterior 2 R)
  (hp : ∀ w ∈ p.support, w ∉ B) :
-- imply
  ∃ (e' : Site 2) (p' : (hypercubicLattice 2).Walk z e'), (∀ w ∈ p'.support, w ∉ B) ∧ e' ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.arcxc_reachesExterior_of_walk heExt p hp

/--
[arcxc_reachesExterior_of_rowClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_reachesExterior_of_rowClear_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {z : Site 2}
-- given
  (hrow : ∀ t : ℤ, t ∈ Set.uIcc (z 0) ((R : ℤ) + 1) → (![t, z 1] : Site 2) ∉ B) :
-- imply
  ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk z e), (∀ w ∈ p.support, w ∉ B) ∧ e ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.arcxc_reachesExterior_of_rowClear hrow

/--
[arcxc_reachesExterior_of_col_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_reachesExterior_of_col_ge_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {z : Site 2}
-- given
  (hB : B ⊆ box 2 R)
  (hzcol : (R : ℤ) ≤ z 0)
  (hzoff : z ∉ B) :
-- imply
  ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk z e), (∀ w ∈ p.support, w ∉ B) ∧ e ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.arcxc_reachesExterior_of_col_ge hB hzcol hzoff

/--
[arcxc_singlePoint_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_singlePoint_reachesExterior_eq
  {u : Site 2}
  {R : ℕ}
-- given
  (hu : u ∈ box 2 R) :
-- imply
  arcxc_ReachesExterior ({u} : Set (Site 2)) R := by
-- proof
  apply StatMech.Lattice.arcxc_singlePoint_reachesExterior u hu

/--
[arcxc_singlePoint_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_singlePoint_connected_eq
  {u : Site 2} :
-- imply
  arcns_OffSupportConnected ({u} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.arcxc_singlePoint_connected u

/--
[arcxc_leafRemovable_of_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_leafRemovable_of_reachesExterior_eq
  {S : Set (Site 2)}
  {u' : Site 2}
  {R : ℕ}
-- given
  (h : arcxc_ReachesExterior (insert u' S) R) :
-- imply
  arcns_LeafRemovable S u' := by
-- proof
  apply StatMech.Lattice.arcxc_leafRemovable_of_reachesExterior h

/--
[arcxc_offSupportConnected_of_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_offSupportConnected_of_reachesExterior_eq
  {B : Set (Site 2)}
-- given
  (h : ∃ R : ℕ, arcxc_ReachesExterior B R) :
-- imply
  arcns_OffSupportConnected B := by
-- proof
  apply StatMech.Lattice.arcxc_offSupportConnected_of_reachesExterior h

/--
[arcxc_exterior_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_exterior_reachesExterior_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {z : Site 2}
-- given
  (hB : B ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk z e), (∀ w ∈ p.support, w ∉ B) ∧ e ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.arcxc_exterior_reachesExterior hB hz

/--
[arcxc_rowClear_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_rowClear_reachesExterior_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {z : Site 2}
-- given
  (hrow : ∀ t : ℤ, t ∈ Set.uIcc (z 0) ((R : ℤ) + 1) → (![t, z 1] : Site 2) ∉ B) :
-- imply
  ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk z e), (∀ w ∈ p.support, w ∉ B) ∧ e ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.arcxc_rowClear_reachesExterior hrow

/--
[arcxc_reachesExterior_of_allRowClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_reachesExterior_of_allRowClear_eq
  {B : Set (Site 2)}
  {R : ℕ}
-- given
  (hB : B ⊆ box 2 R)
  (hall : ∀ z : Site 2, z ∉ B → ∀ t : ℤ, t ∈ Set.uIcc (z 0) ((R : ℤ) + 1) → (![t, z 1] : Site 2) ∉ B) :
-- imply
  arcxc_ReachesExterior B R := by
-- proof
  apply StatMech.Lattice.arcxc_reachesExterior_of_allRowClear hB hall

/--
[arcxc_singlePoint_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean)
-/
@[path]
private lemma arcxc_singlePoint_nonvacuous_eq :
-- imply
  (ffc_offSupportLattice ({![0, 0]} : Set (Site 2))).Reachable ![1, 0] ![0, 1] := by
-- proof
  apply StatMech.Lattice.arcxc_singlePoint_nonvacuous


-- created on 2026-10-23
