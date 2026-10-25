import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc_extremeCell_up_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_earanchor.lean)
-/
@[path]
private lemma jc_extremeCell_up_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  c + ![0, 1] ∉ K := by
-- proof
  apply StatMech.Walls.jc_extremeCell_up_nmem K c hc

/--
[jc_extremeCell_left_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_earanchor.lean)
-/
@[path]
private lemma jc_extremeCell_left_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  c + ![-1, 0] ∉ K := by
-- proof
  apply StatMech.Walls.jc_extremeCell_left_nmem K c hc

/--
[jc_extremeCell_neighbor_right_or_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_earanchor.lean)
-/
@[path]
private lemma jc_extremeCell_neighbor_right_or_down_eq
  {K : Set (Site 2)}
  {c v : Site 2}
-- given
  (hc : IsExtremeCell K c)
  (hv : v ∈ K)
  (hadj : (hypercubicLattice 2).Adj v c) :
-- imply
  v = c + ![1, 0] ∨ v = c + ![0, -1] := by
-- proof
  apply StatMech.Walls.jc_extremeCell_neighbor_right_or_down K c v hc hv hadj

/--
[jc_extremeCell_isAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_earanchor.lean)
-/
@[path]
private lemma jc_extremeCell_isAnchor_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  jc_EarAnchor K c where isExtreme := by
-- proof
  apply StatMech.Walls.jc_extremeCell_isAnchor K c hc

/--
[jc_earAnchor_isEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_earanchor.lean)
-/
@[path]
private lemma jc_earAnchor_isEar_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (h : jc_EarAnchor K c) :
-- imply
  jwd_ExtremeEar K c where isExtreme := by
-- proof
  apply StatMech.Walls.jc_earAnchor_isEar h

/--
[jc_earAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_earanchor.lean)
-/
@[path]
private lemma jc_earAnchor_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c, jc_EarAnchor K c := by
-- proof
  apply StatMech.Walls.jc_earAnchor K hK hne

/--
[jc_earAnchor_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_earanchor.lean)
-/
@[path]
private lemma jc_earAnchor_explicit_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c, c ∈ K ∧ IsBoundaryDart K (leftDart c) ∧ turnZ K (leftDart c) = -1 ∧ (∀ v ∈ K, lexKey v ≤ lexKey c) ∧ (∀ v ∈ K, (hypercubicLattice 2).Adj v c → v = c + ![1, 0] ∨ v = c + ![0, -1]) := by
-- proof
  apply StatMech.Walls.jc_earAnchor_explicit K hK hne

/--
[jc_unitCell_earAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_earanchor.lean)
-/
@[path]
private lemma jc_unitCell_earAnchor_eq :
-- imply
  ∃ c, jc_EarAnchor unitCell c := by
-- proof
  apply StatMech.Walls.jc_unitCell_earAnchor


-- created on 2026-10-23
