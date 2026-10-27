import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailUniqueness
open Finset Filter Topology Matrix StatMech StatMech.FrontierD


/--
[sixVertexBetheSolution_unique_of_diagonalDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailUniqueness.lean)
-/
@[path]
private lemma sixVertexBetheSolution_unique_of_diagonalDominance_eq
  {N n : Nat}
  {c : Real}
  {p q : Fin n → Real}
-- given
  (hc : 2 < c)
  (hdom : 2 * ((n : Real) - 1) * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) < (N : Real))
  (hp : SixVertexSatisfiesBetheEquations c N n p)
  (hq : SixVertexSatisfiesBetheEquations c N n q) :
-- imply
  p = q := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_unique_of_diagonalDominance hc hdom hp hq

/--
[sixVertexBetheSolution_unique_of_anisotropyMagnitude](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailUniqueness.lean)
-/
@[path]
private lemma sixVertexBetheSolution_unique_of_anisotropyMagnitude_eq
  {N n : Nat}
  {c : Real}
  {p q : Fin n → Real}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n ≤ N)
  (htail : (n : Real) < sixVertexAnisotropyMagnitude c)
  (hp : SixVertexSatisfiesBetheEquations c N n p)
  (hq : SixVertexSatisfiesBetheEquations c N n q) :
-- imply
  p = q := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_unique_of_anisotropyMagnitude hc hhalf htail hp hq


-- created on 2026-10-23
