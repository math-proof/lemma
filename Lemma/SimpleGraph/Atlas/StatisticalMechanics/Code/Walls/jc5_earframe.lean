import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc5_earframe
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc5_earCell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earCell_eq_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  jc5_earCell c len = c + ![len, 0] := by
-- proof
  apply StatMech.Walls.jc5_earCell_eq c len

/--
[jc5_earCell_eq_runRightEnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earCell_eq_runRightEnd_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  jc5_earCell c len = jc3_runRightEnd c len := by
-- proof
  apply StatMech.Walls.jc5_earCell_eq_runRightEnd c len

/--
[jc5_earCell_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earCell_coord1_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  (jc5_earCell c len) 1 = c 1 := by
-- proof
  apply StatMech.Walls.jc5_earCell_coord1 c len

/--
[jc5_earUp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earUp_eq_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  jc5_earUp c len = c + ![len, 1] := by
-- proof
  apply StatMech.Walls.jc5_earUp_eq c len

/--
[jc5_earRight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earRight_eq_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  jc5_earRight c len = c + ![len + 1, 0] := by
-- proof
  apply StatMech.Walls.jc5_earRight_eq c len

/--
[jc5_earShelf_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earShelf_eq_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  jc5_earShelf c len = c + ![len, -1] := by
-- proof
  apply StatMech.Walls.jc5_earShelf_eq c len

/--
[jc5_earShelf_eq_downCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earShelf_eq_downCell_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  jc5_earShelf c len = jc3_downCell c len := by
-- proof
  apply StatMech.Walls.jc5_earShelf_eq_downCell c len

/--
[jc5_earUp_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earUp_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hframe : jc2_RunFrame K c len) :
-- imply
  jc5_earUp c len ∉ K := by
-- proof
  apply StatMech.Walls.jc5_earUp_nmem K c len hframe

/--
[jc5_earRight_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earRight_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hframe : jc2_RunFrame K c len) :
-- imply
  jc5_earRight c len ∉ K := by
-- proof
  apply StatMech.Walls.jc5_earRight_nmem K c len hframe

/--
[jc5_earShelf_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earShelf_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hthick : jc2_FullyThick K c len)
  (hlen : 0 ≤ len) :
-- imply
  jc5_earShelf c len ∈ K := by
-- proof
  apply StatMech.Walls.jc5_earShelf_mem K c len hthick hlen

/--
[jc5_earShelf_ne_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earShelf_ne_ear_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  jc5_earShelf c len ≠ jc5_earCell c len := by
-- proof
  apply StatMech.Walls.jc5_earShelf_ne_ear c len

/--
[jc5_earShelf_mem_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earShelf_mem_diff_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hthick : jc2_FullyThick K c len)
  (hlen : 0 ≤ len) :
-- imply
  jc5_earShelf c len ∈ K \ {jc5_earCell c len} := by
-- proof
  apply StatMech.Walls.jc5_earShelf_mem_diff K c len hthick hlen

/--
[jc5_earShelf_adj_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earShelf_adj_ear_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (jc5_earCell c len) (jc5_earShelf c len) := by
-- proof
  apply StatMech.Walls.jc5_earShelf_adj_ear c len

/--
[jc5_EarFrame.isExtreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma isExtreme_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (h : jc5_EarFrame K c len) :
-- imply
  IsExtremeCell K c := by
-- proof
  apply StatMech.Walls.jc5_EarFrame.isExtreme h

/--
[jc5_EarFrame.no_run_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma no_run_up_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (h : jc5_EarFrame K c len) :
-- imply
  ∀ j : ℤ, (c + ![j, 1]) ∉ K := by
-- proof
  apply StatMech.Walls.jc5_EarFrame.no_run_up h

/--
[jc5_EarFrame.len_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma len_nonneg_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (h : jc5_EarFrame K c len) :
-- imply
  0 ≤ len := by
-- proof
  apply StatMech.Walls.jc5_EarFrame.len_nonneg h

/--
[jc5_EarFrame.ear_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma ear_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (h : jc5_EarFrame K c len) :
-- imply
  jc5_earCell c len ∈ K := by
-- proof
  apply StatMech.Walls.jc5_EarFrame.ear_mem h

/--
[jc5_EarFrame.shelf_mem_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma shelf_mem_diff_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (h : jc5_EarFrame K c len) :
-- imply
  jc5_earShelf c len ∈ K \ {jc5_earCell c len} := by
-- proof
  apply StatMech.Walls.jc5_EarFrame.shelf_mem_diff h

/--
[jc5_earFrame_of_runFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earFrame_of_runFrame_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hframe : jc2_RunFrame K c len)
  (hthick : jc2_FullyThick K c len) :
-- imply
  jc5_EarFrame K c len where isFramedRun := by
-- proof
  apply StatMech.Walls.jc5_earFrame_of_runFrame K c len hframe hthick

/--
[jc5_earFrame_of_extremeCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earFrame_of_extremeCell_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c)
  (hthick : jc2_FullyThick K c (jc_runMax K c : ℤ)) :
-- imply
  jc5_EarFrame K c (jc_runMax K c : ℤ) := by
-- proof
  apply StatMech.Walls.jc5_earFrame_of_extremeCell K hK c hc hthick

/--
[jc5_earFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earFrame_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty)
  (hthick : ∀ c, IsExtremeCell K c → jc2_FullyThick K c (jc_runMax K c : ℤ)) :
-- imply
  ∃ c len, jc5_EarFrame K c len := by
-- proof
  apply StatMech.Walls.jc5_earFrame K hK hne hthick

/--
[jc5_earFrame_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earFrame_explicit_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hframe : jc2_RunFrame K c len)
  (hthick : jc2_FullyThick K c len) :
-- imply
  jc5_earCell c len ∈ K ∧ jc5_earUp c len ∉ K ∧ jc5_earRight c len ∉ K ∧ jc5_earShelf c len ∈ K ∧ jc5_earShelf c len ∈ K \ {jc5_earCell c len} ∧ (hypercubicLattice 2).Adj (jc5_earCell c len) (jc5_earShelf c len) := by
-- proof
  apply StatMech.Walls.jc5_earFrame_explicit K c len hframe hthick

/--
[jc5_earFrame_convexCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_earFrame_convexCorner_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hframe : jc2_RunFrame K c len)
  (hthick : jc2_FullyThick K c len) :
-- imply
  (jc5_earCell c len + ![0, 1] ∉ K) ∧ (jc5_earCell c len + ![1, 0] ∉ K) ∧ (jc5_earCell c len + ![0, -1] ∈ K) := by
-- proof
  apply StatMech.Walls.jc5_earFrame_convexCorner K c len hframe hthick

/--
[jc5_block2_isTopRowRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_block2_isTopRowRun_eq :
-- imply
  jc_IsTopRowRun jc2_block2 (![0, 1] : Site 2) 1 where isExtreme := by
-- proof
  apply StatMech.Walls.jc5_block2_isTopRowRun

/--
[jc5_block2_runFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_block2_runFrame_eq :
-- imply
  jc2_RunFrame jc2_block2 (![0, 1] : Site 2) 1 := by
-- proof
  apply StatMech.Walls.jc5_block2_runFrame

/--
[jc5_block2_earFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_block2_earFrame_eq :
-- imply
  jc5_EarFrame jc2_block2 (![0, 1] : Site 2) 1 := by
-- proof
  apply StatMech.Walls.jc5_block2_earFrame

/--
[jc5_block2_convexCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean)
-/
@[path]
private lemma jc5_block2_convexCorner_eq :
-- imply
  (jc5_earCell (![0, 1] : Site 2) 1 + ![0, 1] ∉ jc2_block2) ∧ (jc5_earCell (![0, 1] : Site 2) 1 + ![1, 0] ∉ jc2_block2) ∧ (jc5_earCell (![0, 1] : Site 2) 1 + ![0, -1] ∈ jc2_block2) := by
-- proof
  apply StatMech.Walls.jc5_block2_convexCorner


-- created on 2026-10-23
