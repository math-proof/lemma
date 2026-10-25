import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinpendant
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc2_adj_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinpendant.lean)
-/
@[path]
private lemma jc2_adj_cases_eq
  {v w : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj v w) :
-- imply
  v = w + ![1, 0] ∨ v = w + ![-1, 0] ∨ v = w + ![0, 1] ∨ v = w + ![0, -1] := by
-- proof
  apply StatMech.Walls.jc2_adj_cases v w hadj

/--
[jc2_shift_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinpendant.lean)
-/
@[path]
private lemma jc2_shift_add_eq
  {c : Site 2}
  {i j : ℤ} :
-- imply
  (c + ![i, 0] : Site 2) + ![j, 0] = c + ![i + j, 0] := by
-- proof
  apply StatMech.Walls.jc2_shift_add c i j

/--
[jc2_thinPendant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinpendant.lean)
-/
@[path]
private lemma jc2_thinPendant_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {L : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c L)
  (hlen : 1 ≤ L)
  (hdown : (c + ![L, 0] : Site 2) + ![0, -1] ∉ K) :
-- imply
  jc_IsPendantCell K (c + ![L, 0]) := by
-- proof
  apply StatMech.Walls.jc2_thinPendant K c L hrun hlen hdown

/--
[jc2_thinPendant_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinpendant.lean)
-/
@[path]
private lemma jc2_thinPendant_explicit_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {L : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c L)
  (hlen : 1 ≤ L)
  (hdown : (c + ![L, 0] : Site 2) + ![0, -1] ∉ K) :
-- imply
  (c + ![L, 0] : Site 2) ∈ K ∧ (c + ![L - 1, 0] : Site 2) ∈ K ∧ (hypercubicLattice 2).Adj (c + ![L, 0]) (c + ![L - 1, 0]) ∧ ∀ w : Site 2, w ∈ K ∧ (hypercubicLattice 2).Adj (c + ![L, 0]) w → w = c + ![L - 1, 0] := by
-- proof
  apply StatMech.Walls.jc2_thinPendant_explicit K c L hrun hlen hdown

/--
[jc2_domino_thinPendant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinpendant.lean)
-/
@[path]
private lemma jc2_domino_thinPendant_eq :
-- imply
  jc_IsPendantCell domino ((![0, 0] : Site 2) + ![1, 0]) := by
-- proof
  apply StatMech.Walls.jc2_domino_thinPendant

/--
[jc2_unitCell_runFrame_smoke](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinpendant.lean)
-/
@[path]
private lemma jc2_unitCell_runFrame_smoke_eq :
-- imply
  jc_IsTopRowRun unitCell (![0, 0] : Site 2) 0 := by
-- proof
  apply StatMech.Walls.jc2_unitCell_runFrame_smoke


-- created on 2026-10-23
