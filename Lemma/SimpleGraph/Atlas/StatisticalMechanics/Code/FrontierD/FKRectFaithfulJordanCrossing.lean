import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulJordanCrossing
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectFaithful_bottomTop_leftRight_support_intersects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulJordanCrossing.lean)
-/
@[path]
private lemma fkRectFaithful_bottomTop_leftRight_support_intersects_eq
  {alpha beta lower upper bottomX topX : Int}
  {V : (hypercubicLattice 2).Walk ![bottomX, lower] ![topX, upper]}
  {x y : Site 2}
  {W : (hypercubicLattice 2).Walk x y}
-- given
  (hAlphaBeta : alpha < beta)
  (hLowerUpper : lower <= upper)
  (hBottomLeft : alpha <= bottomX)
  (hBottomRight : bottomX <= beta)
  (hTopLeft : alpha <= topX)
  (hTopRight : topX <= beta)
  (hVBox : ∀ z ∈ V.support, z ∈ rect alpha beta lower upper)
  (hx : x ∈ rect alpha beta lower upper)
  (hy : y ∈ rect alpha beta lower upper)
  (hxLeft : x 0 = alpha)
  (hyRight : y 0 = beta)
  (hWBox : ∀ z ∈ W.support, z ∈ rect alpha beta lower upper) :
-- imply
  ∃ z, z ∈ W.support ∧ z ∈ V.support := by
-- proof
  apply StatMech.FrontierD.fkRectFaithful_bottomTop_leftRight_support_intersects alpha beta lower upper bottomX topX hAlphaBeta hLowerUpper hBottomLeft hBottomRight hTopLeft hTopRight V hVBox hx hy hxLeft hyRight W hWBox


-- created on 2026-10-23
