import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc6_ivt.Part2
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[jc6_walk_step_coord_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_walk_step_coord_le_one_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {i : ℕ}
  {k : Fin 2}
-- given
  (hi : i < w.length) :
-- imply
  ((w.getVert i) k - (w.getVert (i + 1)) k).natAbs ≤ 1 := by
-- proof
  apply StatMech.Walls.jc6_walk_step_coord_le_one w hi k

/--
[jc6_walk_visits_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_walk_visits_row_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {r : ℤ}
-- given
  (hr1 : min (a 1) (b 1) ≤ r)
  (hr2 : r ≤ max (a 1) (b 1)) :
-- imply
  ∃ p ∈ w.support, p 1 = r := by
-- proof
  apply StatMech.Walls.jc6_walk_visits_row w r hr1 hr2

/--
[jc6_walk_visits_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_walk_visits_col_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {r : ℤ}
-- given
  (hr1 : min (a 0) (b 0) ≤ r)
  (hr2 : r ≤ max (a 0) (b 0)) :
-- imply
  ∃ p ∈ w.support, p 0 = r := by
-- proof
  apply StatMech.Walls.jc6_walk_visits_col w r hr1 hr2

/--
[jc6_walk_no_row_skip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_walk_no_row_skip_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {r : ℤ}
-- given
  (hr1 : min (a 1) (b 1) ≤ r)
  (hr2 : r ≤ max (a 1) (b 1)) :
-- imply
  ∃ p ∈ w.support, p 1 = r := by
-- proof
  apply StatMech.Walls.jc6_walk_no_row_skip w r hr1 hr2

/--
[jc6_walk_cannot_hop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_walk_cannot_hop_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {r : ℤ}
-- given
  (hmiss : ∀ p ∈ w.support, p 1 ≠ r) :
-- imply
  r < min (a 1) (b 1) ∨ max (a 1) (b 1) < r := by
-- proof
  apply StatMech.Walls.jc6_walk_cannot_hop w r hmiss

/--
[jc6_subWalk_visits_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_subWalk_visits_row_eq
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {u v : Site 2}
  {r : ℤ}
-- given
  (hu : u ∈ w.support)
  (hv : v ∈ (w.dropUntil u hu).support)
  (hr1 : min (u 1) (v 1) ≤ r)
  (hr2 : r ≤ max (u 1) (v 1)) :
-- imply
  ∃ p ∈ w.support, p 1 = r := by
-- proof
  apply StatMech.Walls.jc6_subWalk_visits_row w hu hv r hr1 hr2

/--
[jc6_orbit_step_coord_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_orbit_step_coord_le_one_eq
  {K : Set (Site 2)}
  {e : Dart}
  {i : ℕ}
  {k : Fin 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hi : i < (olb_orbitLoop K hK e he).length) :
-- imply
  (((olb_orbitLoop K hK e he).getVert i) k - ((olb_orbitLoop K hK e he).getVert (i + 1)) k).natAbs ≤ 1 := by
-- proof
  apply StatMech.Walls.jc6_orbit_step_coord_le_one K hK e he hi k

/--
[jc6_orbit_subStretch_visits_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_orbit_subStretch_visits_row_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
  {r : ℤ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
  (hr1 : min (u 1) (v 1) ≤ r)
  (hr2 : r ≤ max (u 1) (v 1)) :
-- imply
  ∃ p ∈ (olb_orbitLoop K hK e he).support, p 1 = r := by
-- proof
  apply StatMech.Walls.jc6_orbit_subStretch_visits_row K hK e he hu hv r hr1 hr2

/--
[jc6_orbit_cannot_hop_over_cell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_orbit_cannot_hop_over_cell_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
  {f : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
  (hf1 : min (u 1) (v 1) ≤ f 1)
  (hf2 : f 1 ≤ max (u 1) (v 1)) :
-- imply
  ∃ p ∈ (olb_orbitLoop K hK e he).support, p 1 = f 1 := by
-- proof
  apply StatMech.Walls.jc6_orbit_cannot_hop_over_cell K hK e he hu hv f hf1 hf2

/--
[jc6_orbit_subStretch_cannot_hop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_orbit_subStretch_cannot_hop_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
  {f : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
  (hmiss : ∀ p ∈ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support, p 1 ≠ f 1) :
-- imply
  f 1 < min (u 1) (v 1) ∨ max (u 1) (v 1) < f 1 := by
-- proof
  apply StatMech.Walls.jc6_orbit_subStretch_cannot_hop K hK e he hu hv f hmiss

/--
[jc6_ivt_nonvacuous_middleRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_ivt_nonvacuous_middleRow_eq :
-- imply
  ∃ p ∈ jc6_vArc.support, p 1 = 1 := by
-- proof
  apply StatMech.Walls.jc6_ivt_nonvacuous_middleRow

/--
[jc6_ivt_nonvacuous_cannotHop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean)
-/
@[path]
private lemma jc6_ivt_nonvacuous_cannotHop_eq :
-- imply
  (5 : ℤ) < min ((![0, 0] : Site 2) 1) ((![0, 2] : Site 2) 1) ∨ max ((![0, 0] : Site 2) 1) ((![0, 2] : Site 2) 1) < (5 : ℤ) := by
-- proof
  apply StatMech.Walls.jc6_ivt_nonvacuous_cannotHop


-- created on 2026-10-23
