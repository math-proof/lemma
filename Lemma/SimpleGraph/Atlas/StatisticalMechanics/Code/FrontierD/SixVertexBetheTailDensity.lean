import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailDensity
open StatMech StatMech.FrontierD


/--
[sixVertexFiniteRootDensity_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailDensity.lean)
-/
@[path]
private lemma sixVertexFiniteRootDensity_lower_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N) :
-- imply
  (1 - (n : Real) * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) / N) / (2 * Real.pi) <= sixVertexFiniteRootDensity c N n p x := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteRootDensity_lower hc hN p x

/--
[sixVertexTailFiniteDensityFloor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailDensity.lean)
-/
@[path]
private lemma sixVertexTailFiniteDensityFloor_pos_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  0 < sixVertexTailFiniteDensityFloor c := by
-- proof
  apply StatMech.FrontierD.sixVertexTailFiniteDensityFloor_pos hc htail

/--
[sixVertexTailFiniteDensityFloor_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailDensity.lean)
-/
@[path]
private lemma sixVertexTailFiniteDensityFloor_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : 2 * n <= N) :
-- imply
  sixVertexTailFiniteDensityFloor c <= sixVertexFiniteRootDensity c N n p x := by
-- proof
  apply StatMech.FrontierD.sixVertexTailFiniteDensityFloor_le hc hN hhalf p x

/--
[sixVertexBetheSolution_adjacentSpacing_upper_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailDensity.lean)
-/
@[path]
private lemma sixVertexBetheSolution_adjacentSpacing_upper_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {j : Fin n}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : 2 * (n + 1) <= N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  p j.succ - p j.castSucc <= 1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_adjacentSpacing_upper_tail hc htail hN hhalf hopen hsol j

/--
[sixVertexBetheSolution_boundarySpacing_upper_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailDensity.lean)
-/
@[path]
private lemma sixVertexBetheSolution_boundarySpacing_upper_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  p 0 - (p (Fin.last n) - 2 * Real.pi) <= 1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_boundarySpacing_upper_tail hc htail hN hhalf hopen hsol


-- created on 2026-10-23
