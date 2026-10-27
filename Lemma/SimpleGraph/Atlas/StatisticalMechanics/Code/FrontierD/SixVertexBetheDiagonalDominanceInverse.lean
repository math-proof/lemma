import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheDiagonalDominanceInverse
open Finset Matrix StatMech StatMech.FrontierD


/--
[diagonalMargin_mul_abs_le_abs_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheDiagonalDominanceInverse.lean)
-/
@[path]
private lemma diagonalMargin_mul_abs_le_abs_mulVec_eq
  [Fintype n]
  [DecidableEq n]
  {A : Matrix n n Real}
  {i : n}
  {delta : Real}
-- given
  (x : n -> Real)
  (hmax : forall j, |x j| <= |x i|)
  (hmargin : delta + (∑ j ∈ univ.erase i, |A i j|) <= |A i i|) :
-- imply
  delta * := by
-- proof
  apply StatMech.FrontierD.diagonalMargin_mul_abs_le_abs_mulVec A x i hmax hmargin

/--
[exists_abs_le_abs_mulVec_of_diagonalMargin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheDiagonalDominanceInverse.lean)
-/
@[path]
private lemma exists_abs_le_abs_mulVec_of_diagonalMargin_eq
  [Fintype n]
  [DecidableEq n]
  [Nonempty n]
  {A : Matrix n n Real}
  {delta : Real}
-- given
  (x : n -> Real)
  (hmargin : forall i, delta + (∑ j ∈ univ.erase i, |A i j|) <= |A i i|) :
-- imply
  exists i, (forall j, |x j| <= |x i|) /\ delta * := by
-- proof
  apply StatMech.FrontierD.exists_abs_le_abs_mulVec_of_diagonalMargin A x hmargin


-- created on 2026-10-23
