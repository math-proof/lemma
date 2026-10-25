import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateBoundaryLimit
open StatMech StatMech.FrontierD


/--
[continuousAt_sixVertexBetheLogObservable_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateBoundaryLimit.lean)
-/
@[path]
private lemma continuousAt_sixVertexBetheLogObservable_pi_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ContinuousAt (sixVertexBetheLogObservable c) Real.pi := by
-- proof
  apply StatMech.FrontierD.continuousAt_sixVertexBetheLogObservable_pi hc

/--
[sixVertexBetheLogObservable_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateBoundaryLimit.lean)
-/
@[path]
private lemma sixVertexBetheLogObservable_pi_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheLogObservable c Real.pi = Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheLogObservable_pi hc

/--
[tendsto_sixVertexCanonicalEvenBoundaryHalfRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateBoundaryLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenBoundaryHalfRoot_eq
  {c : Real}
  {s : Nat}
  {i : Fin s}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalEvenBoundaryHalfRoot hc s k i) atTop (nhds Real.pi) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenBoundaryHalfRoot hc s i

/--
[tendsto_sixVertexCanonicalOddBoundaryHalfRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateBoundaryLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddBoundaryHalfRoot_eq
  {c : Real}
  {s : Nat}
  {i : Fin (s + 1)}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalOddBoundaryHalfRoot hc s k i) atTop (nhds Real.pi) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddBoundaryHalfRoot hc s i

/--
[tendsto_sum_sixVertexCanonicalEvenBoundaryLogObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateBoundaryLimit.lean)
-/
@[path]
private lemma tendsto_sum_sixVertexCanonicalEvenBoundaryLogObservable_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => ∑ i : Fin s, sixVertexBetheLogObservable c (sixVertexCanonicalEvenBoundaryHalfRoot hc s k i)) atTop (nhds ((s : Real) * Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sum_sixVertexCanonicalEvenBoundaryLogObservable hc s

/--
[tendsto_sum_sixVertexCanonicalOddBoundaryLogObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateBoundaryLimit.lean)
-/
@[path]
private lemma tendsto_sum_sixVertexCanonicalOddBoundaryLogObservable_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => ∑ i : Fin (s + 1), sixVertexBetheLogObservable c (sixVertexCanonicalOddBoundaryHalfRoot hc s k i)) atTop (nhds ((s + 1 : Real) * Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sum_sixVertexCanonicalOddBoundaryLogObservable hc s


-- created on 2026-10-23
