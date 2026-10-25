import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryHorizontalParity
open StatMech StatMech.FrontierD


/--
[fkRectHorizontalOddOrZero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryHorizontalParity.lean)
-/
@[path]
private lemma fkRectHorizontalOddOrZero_zero_eq :
-- imply
  FKRectHorizontalOddOrZero (0, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalOddOrZero_zero

/--
[FKRectHorizontalOddOrZero.snd_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryHorizontalParity.lean)
-/
@[path]
private lemma snd_eq_zero_eq
  {u : Int × Int}
-- given
  (hu : FKRectHorizontalOddOrZero u) :
-- imply
  u.2 = 0 := by
-- proof
  apply StatMech.FrontierD.FKRectHorizontalOddOrZero.snd_eq_zero hu

/--
[FKRectHorizontalOddOrZero.odd_fst_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryHorizontalParity.lean)
-/
@[path]
private lemma odd_fst_of_ne_zero_eq
  {u : Int × Int}
-- given
  (hu : FKRectHorizontalOddOrZero u)
  (hne : u ≠ 0) :
-- imply
  Odd u.1 := by
-- proof
  apply StatMech.FrontierD.FKRectHorizontalOddOrZero.odd_fst_of_ne_zero hu hne

/--
[fkRectHorizontalOddOrZero_add_eq_zero_of_both_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryHorizontalParity.lean)
-/
@[path]
private lemma fkRectHorizontalOddOrZero_add_eq_zero_of_both_ne_zero_eq
  {u v : Int × Int}
-- given
  (hu : FKRectHorizontalOddOrZero u)
  (hv : FKRectHorizontalOddOrZero v)
  (hsum : FKRectHorizontalOddOrZero (u + v))
  (hu0 : u ≠ 0)
  (hv0 : v ≠ 0) :
-- imply
  u + v = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalOddOrZero_add_eq_zero_of_both_ne_zero hu hv hsum hu0 hv0

/--
[fkRectHorizontalOddOrZero_split_one_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryHorizontalParity.lean)
-/
@[path]
private lemma fkRectHorizontalOddOrZero_split_one_eq_zero_eq
  {u v w : Int × Int}
-- given
  (hu : FKRectHorizontalOddOrZero u)
  (hv : FKRectHorizontalOddOrZero v)
  (hw : FKRectHorizontalOddOrZero w)
  (hu0 : u ≠ 0)
  (hsplit : u = v + w) :
-- imply
  v = 0 ∨ w = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalOddOrZero_split_one_eq_zero hu hv hw hu0 hsplit


-- created on 2026-10-23
