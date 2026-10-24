import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.EarExistence
open SimpleGraph Function StatMech StatMech.Lattice


/--
[unitWt_negx](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma unitWt_negx_eq :
-- imply
  unitWt (![-1, 0] : Site 2) = 1 := by
-- proof
  apply StatMech.Lattice.unitWt_negx

/--
[leftDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma leftDart_tail_eq
  {c : Site 2} :
-- imply
  (leftDart c).tail = c := by
-- proof
  apply StatMech.Lattice.leftDart_tail c

/--
[leftDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma leftDart_dir_eq
  {c : Site 2} :
-- imply
  (leftDart c).dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.leftDart_dir c

/--
[leftDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma leftDart_head_eq
  {c : Site 2} :
-- imply
  (leftDart c).head = c + ![-1, 0] := by
-- proof
  apply StatMech.Lattice.leftDart_head c

/--
[leftDart_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma leftDart_travel_eq
  {c : Site 2} :
-- imply
  -rot90Fun (leftDart c).dir = ![0, 1] := by
-- proof
  apply StatMech.Lattice.leftDart_travel c

/--
[leftDart_head_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma leftDart_head_coord0_eq
  {c : Site 2} :
-- imply
  (leftDart c).head 0 = c 0 - 1 := by
-- proof
  apply StatMech.Lattice.leftDart_head_coord0 c

/--
[leftDart_head_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma leftDart_head_coord1_eq
  {c : Site 2} :
-- imply
  (leftDart c).head 1 = c 1 := by
-- proof
  apply StatMech.Lattice.leftDart_head_coord1 c

/--
[leftDart_front_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma leftDart_front_coord0_eq
  {c : Site 2} :
-- imply
  ((leftDart c).head + (-rot90Fun (leftDart c).dir)) 0 = c 0 - 1 := by
-- proof
  apply StatMech.Lattice.leftDart_front_coord0 c

/--
[leftDart_front_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma leftDart_front_coord1_eq
  {c : Site 2} :
-- imply
  ((leftDart c).head + (-rot90Fun (leftDart c).dir)) 1 = c 1 + 1 := by
-- proof
  apply StatMech.Lattice.leftDart_front_coord1 c

/--
[leftDart_side_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma leftDart_side_coord0_eq
  {c : Site 2} :
-- imply
  ((leftDart c).tail + (-rot90Fun (leftDart c).dir)) 0 = c 0 := by
-- proof
  apply StatMech.Lattice.leftDart_side_coord0 c

/--
[leftDart_side_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma leftDart_side_coord1_eq
  {c : Site 2} :
-- imply
  ((leftDart c).tail + (-rot90Fun (leftDart c).dir)) 1 = c 1 + 1 := by
-- proof
  apply StatMech.Lattice.leftDart_side_coord1 c

/--
[exists_extremeCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma exists_extremeCell_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c, IsExtremeCell K c := by
-- proof
  apply StatMech.Lattice.exists_extremeCell K hK hne

/--
[extremeCell_not_mem_of_higher](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma extremeCell_not_mem_of_higher_eq
  {K : Set (Site 2)}
  {c v : Site 2}
-- given
  (hc : IsExtremeCell K c)
  (hy : c 1 < v 1) :
-- imply
  v ∉ K := by
-- proof
  apply StatMech.Lattice.extremeCell_not_mem_of_higher K c v hc hy

/--
[extremeCell_not_mem_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma extremeCell_not_mem_of_left_eq
  {K : Set (Site 2)}
  {c v : Site 2}
-- given
  (hc : IsExtremeCell K c)
  (hy : v 1 = c 1)
  (hx : v 0 < c 0) :
-- imply
  v ∉ K := by
-- proof
  apply StatMech.Lattice.extremeCell_not_mem_of_left K c v hc hy hx

/--
[extremeCell_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma extremeCell_front_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  (leftDart c).head + (-rot90Fun (leftDart c).dir) ∉ K := by
-- proof
  apply StatMech.Lattice.extremeCell_front_nmem K c hc

/--
[extremeCell_side_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma extremeCell_side_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  (leftDart c).tail + (-rot90Fun (leftDart c).dir) ∉ K := by
-- proof
  apply StatMech.Lattice.extremeCell_side_nmem K c hc

/--
[extremeCell_head_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma extremeCell_head_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  (leftDart c).head ∉ K := by
-- proof
  apply StatMech.Lattice.extremeCell_head_nmem K c hc

/--
[extremeCell_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma extremeCell_boundary_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  IsBoundaryDart K (leftDart c) := by
-- proof
  apply StatMech.Lattice.extremeCell_boundary K c hc

/--
[extremeCell_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma extremeCell_turnZ_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  turnZ K (leftDart c) = -1 := by
-- proof
  apply StatMech.Lattice.extremeCell_turnZ K c hc

/--
[exists_convex_corner_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma exists_convex_corner_dart_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 := by
-- proof
  apply StatMech.Lattice.exists_convex_corner_dart K hK hne

/--
[one_le_leftCornerCount_of_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma one_le_leftCornerCount_of_first_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ}
-- given
  (hp : 0 < p)
  (h0 : turnZ K e = -1) :
-- imply
  1 ≤ leftCornerCount K e p := by
-- proof
  apply StatMech.Lattice.one_le_leftCornerCount_of_first K e p hp h0

/--
[extremeCell_orbit_one_le_leftCornerCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma extremeCell_orbit_one_le_leftCornerCount_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  1 ≤ leftCornerCount K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc)) := by
-- proof
  apply StatMech.Lattice.extremeCell_orbit_one_le_leftCornerCount K hK c hc

/--
[extremeCell_orbit_rightCornerCount_lt_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma extremeCell_orbit_rightCornerCount_lt_period_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  rightCornerCount K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc)) < (dartOrbitPeriod K (extremeBase K c hc) : ℤ) := by
-- proof
  apply StatMech.Lattice.extremeCell_orbit_rightCornerCount_lt_period K hK c hc

/--
[removeCell_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma removeCell_finite_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite) :
-- imply
  (K \ {c}).Finite := by
-- proof
  apply StatMech.Lattice.removeCell_finite K hK c

/--
[removeCell_ncard_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma removeCell_ncard_lt_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : c ∈ K) :
-- imply
  (K \ {c}).ncard < K.ncard := by
-- proof
  apply StatMech.Lattice.removeCell_ncard_lt K hK c hc

/--
[removeExtremeCell_ncard_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean)
-/
@[path]
private lemma removeExtremeCell_ncard_lt_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  (K \ {c}).ncard < K.ncard := by
-- proof
  apply StatMech.Lattice.removeExtremeCell_ncard_lt K hK c hc


-- created on 2026-10-23
