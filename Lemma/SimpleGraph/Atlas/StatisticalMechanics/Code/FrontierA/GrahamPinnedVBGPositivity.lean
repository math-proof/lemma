import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGPositivity
open Finset Classical StatMech StatMech.FrontierA


/--
[grahamPinnedProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGPositivity.lean)
-/
@[path]
private lemma grahamPinnedProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  (0 : ConfigSpace V -> Real) <= grahamPinnedProb E J m := by
-- proof
  apply StatMech.FrontierA.grahamPinnedProb_nonneg E J m

/--
[grahamPinnedProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGPositivity.lean)
-/
@[path]
private lemma grahamPinnedProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  ∑ s, grahamPinnedProb E J m s = 1 := by
-- proof
  apply StatMech.FrontierA.grahamPinnedProb_sum_eq_one E J m

/--
[grahamPinned_coordUp_pos_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGPositivity.lean)
-/
@[path]
private lemma grahamPinned_coordUp_pos_lt_one_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m k : V}
-- given
  (J : Sym2 V -> Real)
  (hmk : m ≠ k) :
-- imply
  0 < vbg_exp (grahamPinnedProb E J m) (vbg_coordUp k) ∧ vbg_exp (grahamPinnedProb E J m) (vbg_coordUp k) < 1 := by
-- proof
  apply StatMech.FrontierA.grahamPinned_coordUp_pos_lt_one E J hmk


-- created on 2026-10-23
