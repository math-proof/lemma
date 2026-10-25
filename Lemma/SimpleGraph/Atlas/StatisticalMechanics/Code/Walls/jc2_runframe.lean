import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc2_isTopRowRun_of_extremeCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma jc2_isTopRowRun_of_extremeCell_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  jc_IsTopRowRun K c (jc_runMax K c : ℤ) where isExtreme := by
-- proof
  apply StatMech.Walls.jc2_isTopRowRun_of_extremeCell K hK c hc

/--
[jc2_RunFrame.isExtreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma isExtreme_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (h : jc2_RunFrame K c len) :
-- imply
  IsExtremeCell K c := by
-- proof
  apply StatMech.Walls.jc2_RunFrame.isExtreme h

/--
[jc2_RunFrame.len_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma len_nonneg_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (h : jc2_RunFrame K c len) :
-- imply
  0 ≤ len := by
-- proof
  apply StatMech.Walls.jc2_RunFrame.len_nonneg h

/--
[jc2_RunFrame.run_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma run_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
  {j : ℤ}
-- given
  (h : jc2_RunFrame K c len)
  (hj0 : 0 ≤ j)
  (hj1 : j ≤ len) :
-- imply
  (c + ![j, 0]) ∈ K := by
-- proof
  apply StatMech.Walls.jc2_RunFrame.run_mem h j hj0 hj1

/--
[jc2_RunFrame.mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (h : jc2_RunFrame K c len) :
-- imply
  c ∈ K := by
-- proof
  apply StatMech.Walls.jc2_RunFrame.mem h

/--
[jc2_runFrame_of_extremeCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma jc2_runFrame_of_extremeCell_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  jc2_RunFrame K c (jc_runMax K c : ℤ) := by
-- proof
  apply StatMech.Walls.jc2_runFrame_of_extremeCell K hK c hc

/--
[jc2_runFrame_of_earAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma jc2_runFrame_of_earAnchor_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hanchor : jc_EarAnchor K c) :
-- imply
  jc2_RunFrame K c (jc_runMax K c : ℤ) := by
-- proof
  apply StatMech.Walls.jc2_runFrame_of_earAnchor K hK hanchor

/--
[jc2_runFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma jc2_runFrame_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c len, jc2_RunFrame K c len := by
-- proof
  apply StatMech.Walls.jc2_runFrame K hK hne

/--
[jc2_runFrame_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma jc2_runFrame_explicit_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c len, c ∈ K ∧ 0 ≤ len ∧ (∀ j : ℤ, 0 ≤ j → j ≤ len → (c + ![j, 0]) ∈ K) ∧ (c + ![len + 1, 0]) ∉ K ∧ (∀ j : ℤ, (c + ![j, 1]) ∉ K) ∧ (c + ![(-1 : ℤ), 0]) ∉ K := by
-- proof
  apply StatMech.Walls.jc2_runFrame_explicit K hK hne

/--
[jc2_runFrame_anchored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma jc2_runFrame_anchored_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c len, IsExtremeCell K c ∧ jc2_RunFrame K c len := by
-- proof
  apply StatMech.Walls.jc2_runFrame_anchored K hK hne

/--
[jc2_domino_runFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma jc2_domino_runFrame_eq :
-- imply
  jc2_RunFrame domino (![0, 0] : Site 2) 1 := by
-- proof
  apply StatMech.Walls.jc2_domino_runFrame

/--
[jc2_unitCell_runFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean)
-/
@[path]
private lemma jc2_unitCell_runFrame_eq :
-- imply
  jc2_RunFrame unitCell (![0, 0] : Site 2) 0 := by
-- proof
  apply StatMech.Walls.jc2_unitCell_runFrame


-- created on 2026-10-23
