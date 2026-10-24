import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.PathVisitsRow
open Set Finset SimpleGraph StatMech StatMech.Lattice


/--
[pvr_adj_coord_diff_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean)
-/
@[path]
private lemma pvr_adj_coord_diff_le_one_eq
  {d : ℕ}
  {x y : Site d}
  {i : Fin d}
-- given
  (h : (hypercubicLattice d).Adj x y) :
-- imply
  (x i - y i).natAbs ≤ 1 := by
-- proof
  apply StatMech.Lattice.pvr_adj_coord_diff_le_one h i

/--
[pvr_discrete_ivt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean)
-/
@[path]
private lemma pvr_discrete_ivt_eq
  {f : ℕ → ℤ} :
-- imply
  ∀ (n : ℕ), (∀ i, i < n → (f (i + 1) - f i).natAbs ≤ 1) → ∀ r, f 0 ≤ r → r ≤ f n → ∃ i ≤ n, f i = r := by
-- proof
  apply StatMech.Lattice.pvr_discrete_ivt f

/--
[pvr_exists_idx_at_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean)
-/
@[path]
private lemma pvr_exists_idx_at_coord_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {k : Fin 2}
  {c d : ℤ}
  {r : ℤ}
-- given
  (hac : a k = c)
  (hbd : b k = d)
  (hcd : c ≤ d)
  (hr1 : c ≤ r)
  (hr2 : r ≤ d) :
-- imply
  ∃ i ≤ w.length, (w.getVert i) k = r := by
-- proof
  apply StatMech.Lattice.pvr_exists_idx_at_coord w k hac hbd hcd r hr1 hr2

/--
[pvr_visits_every_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean)
-/
@[path]
private lemma pvr_visits_every_coord_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {k : Fin 2}
  {c d : ℤ}
  {r : ℤ}
-- given
  (hac : a k = c)
  (hbd : b k = d)
  (hcd : c ≤ d)
  (hr1 : c ≤ r)
  (hr2 : r ≤ d) :
-- imply
  ∃ p ∈ w.support, p k = r := by
-- proof
  apply StatMech.Lattice.pvr_visits_every_coord w k hac hbd hcd r hr1 hr2

/--
[pvr_visits_every_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean)
-/
@[path]
private lemma pvr_visits_every_row_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {c d : ℤ}
  {r : ℤ}
-- given
  (hac : a 1 = c)
  (hbd : b 1 = d)
  (hcd : c ≤ d)
  (hr1 : c ≤ r)
  (hr2 : r ≤ d) :
-- imply
  ∃ p ∈ w.support, p 1 = r := by
-- proof
  apply StatMech.Lattice.pvr_visits_every_row w hac hbd hcd r hr1 hr2

/--
[pvr_visits_every_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean)
-/
@[path]
private lemma pvr_visits_every_col_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {c d : ℤ}
  {r : ℤ}
-- given
  (hac : a 0 = c)
  (hbd : b 0 = d)
  (hcd : c ≤ d)
  (hr1 : c ≤ r)
  (hr2 : r ≤ d) :
-- imply
  ∃ p ∈ w.support, p 0 = r := by
-- proof
  apply StatMech.Lattice.pvr_visits_every_col w hac hbd hcd r hr1 hr2

/--
[pvr_firstIdxAtCoord_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean)
-/
@[path]
private lemma pvr_firstIdxAtCoord_spec_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {k : Fin 2}
  {r : ℤ}
-- given
  (h : ∃ i, (w.getVert i) k = r) :
-- imply
  (w.getVert (pvr_firstIdxAtCoord w k r h)) k = r := by
-- proof
  apply StatMech.Lattice.pvr_firstIdxAtCoord_spec w k r h

/--
[pvr_firstIdxAtCoord_min](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean)
-/
@[path]
private lemma pvr_firstIdxAtCoord_min_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {k : Fin 2}
  {r : ℤ}
  {j : ℕ}
-- given
  (h : ∃ i, (w.getVert i) k = r)
  (hj : j < pvr_firstIdxAtCoord w k r h) :
-- imply
  (w.getVert j) k ≠ r := by
-- proof
  apply StatMech.Lattice.pvr_firstIdxAtCoord_min w k r h hj

/--
[pvr_firstAtRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean)
-/
@[path]
private lemma pvr_firstAtRow_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {c d : ℤ}
  {r : ℤ}
-- given
  (hac : a 1 = c)
  (hbd : b 1 = d)
  (hcd : c ≤ d)
  (hr1 : c ≤ r)
  (hr2 : r ≤ d) :
-- imply
  ∃ i, (w.getVert i) 1 = r ∧ (∀ j, j < i → (w.getVert j) 1 ≠ r) := by
-- proof
  apply StatMech.Lattice.pvr_firstAtRow w hac hbd hcd r hr1 hr2


-- created on 2026-10-23
