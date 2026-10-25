import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePairedBounds
open Finset StatMech StatMech.FrontierD


/--
[sixVertexTheta_zero_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePairedBounds.lean)
-/
@[path]
private lemma sixVertexTheta_zero_pair_eq
  {c q : Real} :
-- imply
  sixVertexTheta c 0 q + sixVertexTheta c 0 (-q) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_zero_pair c q

/--
[sixVertexTheta_symmetric_pair_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePairedBounds.lean)
-/
@[path]
private lemma sixVertexTheta_symmetric_pair_bounds_eq
  {c x : Real}
  {q : Real}
-- given
  (hc : 2 < c)
  (hx : 0 < x)
  (hxpi : x < Real.pi) :
-- imply
  -2 * Real.pi < sixVertexTheta c x q + sixVertexTheta c x (-q) ∧ sixVertexTheta c x q + sixVertexTheta c x (-q) < 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_symmetric_pair_bounds hc hx hxpi q

/--
[sum_sixVertexTheta_symmetric_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePairedBounds.lean)
-/
@[path]
private lemma sum_sixVertexTheta_symmetric_bounds_eq
  {c x : Real}
  {n : Nat}
  {p : Fin n -> Real}
-- given
  (hc : 2 < c)
  (hn : 0 < n)
  (hsymm : SixVertexRootSymmetric p)
  (hx : 0 < x)
  (hxpi : x < Real.pi) :
-- imply
  -(n : Real) * Real.pi < ∑ k, sixVertexTheta c x (p k) ∧ ∑ k, sixVertexTheta c x (p k) < 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexTheta_symmetric_bounds hc hn hsymm hx hxpi

/--
[sixVertexPositiveHalfBetheRoots_quantile_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePairedBounds.lean)
-/
@[path]
private lemma sixVertexPositiveHalfBetheRoots_quantile_upper_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexPositiveHalfBetheRoots hc k j < Real.pi / 2 + Real.pi * (2 * (j : Real) + 1) / (sixVertexFourWidth 0 k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfBetheRoots_quantile_upper hc k j


-- created on 2026-10-23
