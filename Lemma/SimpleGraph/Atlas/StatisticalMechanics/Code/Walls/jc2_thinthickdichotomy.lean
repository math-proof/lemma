import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinthickdichotomy.Part2
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc2_rightEnd_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_rightEnd_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len) :
-- imply
  jc2_rightEnd c len ∈ K := by
-- proof
  apply StatMech.Walls.jc2_rightEnd_mem K c len hrun

/--
[jc2_thin_pendant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_thin_pendant_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len)
  (hlen : 1 ≤ len)
  (hthin : jc2_rightEnd c len + ![0, -1] ∉ K) :
-- imply
  jc_IsPendantCell K (jc2_rightEnd c len) := by
-- proof
  apply StatMech.Walls.jc2_thin_pendant K c len hrun hlen hthin

/--
[jc2_left_down_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_left_down_distinct_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  (c + ![len - 1, 0] : Site 2) ≠ jc2_rightEnd c len + ![0, -1] := by
-- proof
  apply StatMech.Walls.jc2_left_down_distinct c len

/--
[jc2_thick_not_pendant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_thick_not_pendant_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len)
  (hlen : 1 ≤ len)
  (hthick : jc2_rightEnd c len + ![0, -1] ∈ K) :
-- imply
  ¬ jc_IsPendantCell K (jc2_rightEnd c len) := by
-- proof
  apply StatMech.Walls.jc2_thick_not_pendant K c len hrun hlen hthick

/--
[jc2_thin_thick_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_thin_thick_dichotomy_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len)
  (hlen : 1 ≤ len) :
-- imply
  (jc2_rightEnd c len + ![0, -1] ∉ K ∧ jc_IsPendantCell K (jc2_rightEnd c len)) ∨ (jc2_rightEnd c len + ![0, -1] ∈ K ∧ ¬ jc_IsPendantCell K (jc2_rightEnd c len)) := by
-- proof
  apply StatMech.Walls.jc2_thin_thick_dichotomy K c len hrun hlen

/--
[jc2_rightEnd_len_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_rightEnd_len_zero_eq
  {c : Site 2} :
-- imply
  jc2_rightEnd c 0 = c := by
-- proof
  apply StatMech.Walls.jc2_rightEnd_len_zero c

/--
[jc2_len_zero_right_or_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_len_zero_right_or_down_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {v : Site 2}
-- given
  (hrun : jc_IsTopRowRun K c 0)
  (hv : v ∈ K)
  (hadj : (hypercubicLattice 2).Adj v c) :
-- imply
  v = jc2_rightEnd c 0 + ![1, 0] ∨ v = jc2_rightEnd c 0 + ![0, -1] := by
-- proof
  apply StatMech.Walls.jc2_len_zero_right_or_down K c hrun v hv hadj

/--
[jc2_topRowRun_thinThickDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_topRowRun_thinThickDichotomy_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len) :
-- imply
  jc2_ThinThickDichotomy K c len where dichotomy hlen := by
-- proof
  apply StatMech.Walls.jc2_topRowRun_thinThickDichotomy K c len hrun

/--
[jc2_thinThickDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_thinThickDichotomy_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len) :
-- imply
  jc2_ThinThickDichotomy K c len := by
-- proof
  apply StatMech.Walls.jc2_thinThickDichotomy K c len hrun

/--
[jc2_domino_thin_pendant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_domino_thin_pendant_eq :
-- imply
  jc_IsPendantCell domino (jc2_rightEnd (![0, 0] : Site 2) 1) := by
-- proof
  apply StatMech.Walls.jc2_domino_thin_pendant

/--
[jc2_unitCell_len_zero_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean)
-/
@[path]
private lemma jc2_unitCell_len_zero_split_eq :
-- imply
  jc2_ThinThickDichotomy unitCell (![0, 0] : Site 2) 0 := by
-- proof
  apply StatMech.Walls.jc2_unitCell_len_zero_split


-- created on 2026-10-23
