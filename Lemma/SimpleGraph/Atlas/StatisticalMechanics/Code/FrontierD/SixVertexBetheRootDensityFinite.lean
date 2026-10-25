import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityFinite
open Finset StatMech StatMech.FrontierD


/--
[hasDerivAt_sixVertexBetheCountingFunction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityFinite.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexBetheCountingFunction_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N) :
-- imply
  HasDerivAt (sixVertexBetheCountingFunction c N n p) (sixVertexFiniteRootDensity c N n p x) x := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexBetheCountingFunction hc hN p x

/--
[continuous_sixVertexFiniteRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityFinite.lean)
-/
@[path]
private lemma continuous_sixVertexFiniteRootDensity_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
-- given
  (hc : 2 < c) :
-- imply
  Continuous (sixVertexFiniteRootDensity c N n p) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexFiniteRootDensity hc N n p

/--
[sixVertexRootDensityWeight_mul_finiteRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityFinite.lean)
-/
@[path]
private lemma sixVertexRootDensityWeight_mul_finiteRootDensity_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N) :
-- imply
  sixVertexRootDensityWeight c x * sixVertexFiniteRootDensity c N n p x = sixVertexRootDensityWeight c x / (2 * Real.pi) - (∑ k, sixVertexRootDensityKernel c x (p k)) / ((2 * Real.pi) * N) := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityWeight_mul_finiteRootDensity hc hN p x

/--
[sixVertexBetheCountingFunction_at_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityFinite.lean)
-/
@[path]
private lemma sixVertexBetheCountingFunction_at_root_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {j : Fin n}
-- given
  (hN : 0 < N)
  (hsol : SixVertexSatisfiesBetheEquations c N n p) :
-- imply
  sixVertexBetheCountingFunction c N n p (p j) = sixVertexCentralQuantumNumber j / N := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCountingFunction_at_root hN hsol j

/--
[intervalIntegral_sixVertexFiniteRootDensity_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityFinite.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFiniteRootDensity_adjacent_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {j : Fin n}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  ∫ x in p j.castSucc..p j.succ, sixVertexFiniteRootDensity c N (n + 1) p x = 1 / N := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFiniteRootDensity_adjacent hc hN hsol j

/--
[sixVertexBetheCountingFunction_add_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityFinite.lean)
-/
@[path]
private lemma sixVertexBetheCountingFunction_add_two_pi_eq
  {N n : Nat}
  {c : Real}
  {p : Fin n → Real}
  {x : Real}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexBetheCountingFunction c N n p (x + 2 * Real.pi) = sixVertexBetheCountingFunction c N n p x + 1 - (n : Real) / N := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCountingFunction_add_two_pi hN c p x

/--
[intervalIntegral_sixVertexFiniteRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityFinite.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFiniteRootDensity_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N) :
-- imply
  ∫ x in -Real.pi..Real.pi, sixVertexFiniteRootDensity c N n p x = 1 - (n : Real) / N := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFiniteRootDensity hc hN p


-- created on 2026-10-23
