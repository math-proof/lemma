import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc_toprowrun.Part4
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc_shiftX_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_shiftX_coord0_eq
  {c : Site 2}
  {j : ℤ} :
-- imply
  (jc_shiftX c j) 0 = c 0 + j := by
-- proof
  apply StatMech.Walls.jc_shiftX_coord0 c j

/--
[jc_shiftX_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_shiftX_coord1_eq
  {c : Site 2}
  {j : ℤ} :
-- imply
  (jc_shiftX c j) 1 = c 1 := by
-- proof
  apply StatMech.Walls.jc_shiftX_coord1 c j

/--
[jc_shiftX_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_shiftX_zero_eq
  {c : Site 2} :
-- imply
  jc_shiftX c 0 = c := by
-- proof
  apply StatMech.Walls.jc_shiftX_zero c

/--
[jc_zero_mem_runLengths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_zero_mem_runLengths_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : c ∈ K) :
-- imply
  0 ∈ jc_RunLengths K c := by
-- proof
  apply StatMech.Walls.jc_zero_mem_runLengths K c hc

/--
[jc_runLengths_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_runLengths_bddAbove_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite) :
-- imply
  BddAbove (jc_RunLengths K c) := by
-- proof
  apply StatMech.Walls.jc_runLengths_bddAbove K hK c

/--
[jc_runMax_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_runMax_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : c ∈ K) :
-- imply
  jc_runMax K c ∈ jc_RunLengths K c := by
-- proof
  apply StatMech.Walls.jc_runMax_mem K hK c hc

/--
[jc_runMax_succ_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_runMax_succ_not_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite) :
-- imply
  jc_runMax K c + 1 ∉ jc_RunLengths K c := by
-- proof
  apply StatMech.Walls.jc_runMax_succ_not_mem K hK c

/--
[jc_runMax_succ_nmem_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_runMax_succ_nmem_K_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : c ∈ K) :
-- imply
  jc_shiftX c ((jc_runMax K c : ℤ) + 1) ∉ K := by
-- proof
  apply StatMech.Walls.jc_runMax_succ_nmem_K K hK c hc

/--
[jc_extremeCell_topRowRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_extremeCell_topRowRun_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  jc_TopRowRun K c (jc_runMax K c) where isExtreme := by
-- proof
  apply StatMech.Walls.jc_extremeCell_topRowRun K hK c hc

/--
[jc_topRowRun_of_earAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_topRowRun_of_earAnchor_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hanchor : jc_EarAnchor K c) :
-- imply
  jc_TopRowRun K c (jc_runMax K c) := by
-- proof
  apply StatMech.Walls.jc_topRowRun_of_earAnchor K hK hanchor

/--
[jc_topRowRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_topRowRun_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c L, jc_TopRowRun K c L := by
-- proof
  apply StatMech.Walls.jc_topRowRun K hK hne

/--
[jc_topRowRun_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_topRowRun_explicit_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c L, c ∈ K ∧ (∀ j : ℕ, j ≤ L → jc_shiftX c (j : ℤ) ∈ K) ∧ jc_shiftX c ((L : ℤ) + 1) ∉ K ∧ (∀ j : ℕ, (jc_shiftX c (j : ℤ)) 1 = c 1) ∧ (∀ v ∈ K, v 1 ≤ c 1) ∧ jc_shiftX c (-1) ∉ K := by
-- proof
  apply StatMech.Walls.jc_topRowRun_explicit K hK hne

/--
[jc_unitCell_topRowRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean)
-/
@[path]
private lemma jc_unitCell_topRowRun_eq :
-- imply
  ∃ c L, jc_TopRowRun unitCell c L := by
-- proof
  apply StatMech.Walls.jc_unitCell_topRowRun


-- created on 2026-10-23
