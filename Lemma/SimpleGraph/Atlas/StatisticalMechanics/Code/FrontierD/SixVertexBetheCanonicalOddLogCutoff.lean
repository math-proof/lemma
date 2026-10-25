import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogCutoff
open StatMech StatMech.FrontierD


/--
[abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff_additive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogCutoff.lean)
-/
@[path]
private lemma abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff_additive_eq
  {c epsilon delta C D : Real}
  {N n T : Nat}
  {p q : Fin n -> Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hdelta : 0 < delta)
  (hC : 0 <= C)
  (hD : 0 <= D)
  (hN : 0 < N)
  (hp : forall j, p j ∈ Set.Ioo 0 Real.pi)
  (hq : forall j, q j ∈ Set.Ioo 0 Real.pi)
  (hscale : forall j, Real.pi <= (N : Real) * p j)
  (hclose : forall j, |q j - p j| <= p j / 2)
  (hdiff : forall j, |q j - p j| <= C * p j / N + D / (N : Real) ^ 2)
  (hfar : forall j, T <= j.val -> delta <= p j) :
-- imply
  |∑ j, (sixVertexBetheLogRegularizationError c epsilon (q j) - sixVertexBetheLogRegularizationError c epsilon (p j))| <= (T : Real) * ((2 * Real.pi * C + 2 * D) / N) + (n : Real) * ((epsilon * Real.pi ^ 4 / delta ^ 4) * ((C * Real.pi + D) / N)) := by
-- proof
  apply StatMech.FrontierD.abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff_additive hc hepsilon hdelta hC hD hN hp hq hscale hclose hdiff hfar

/--
[eventually_abs_sum_sixVertexCanonicalOddLogRegularizationError_le_cutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogCutoff.lean)
-/
@[path]
private lemma eventually_abs_sum_sixVertexCanonicalOddLogRegularizationError_le_cutoff_eq
  {c epsilon : Real}
  {s : Nat}
  {M : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hM : 0 < M) :
-- imply
  ∀ᶠ k : Nat in atTop, let N := sixVertexFourWidth (2 * s + 1) k let n := s + k + 1 let C := sixVertexCanonicalOddOffsetLinearBound c hc s let D := sixVertexCanonicalOddOffsetRemainderBound c hc s |∑ j : Fin n, (sixVertexBetheLogRegularizationError c epsilon (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) - sixVertexBetheLogRegularizationError c epsilon (sixVertexCanonicalOddMidpointHalfRoot hc s k j))| <= (2 * Real.pi * C + 2 * D) * (1 / M + 1 / N) + epsilon * (C * Real.pi + D) * M ^ 4 / 16 := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sum_sixVertexCanonicalOddLogRegularizationError_le_cutoff hc hepsilon s hM


-- created on 2026-10-23
