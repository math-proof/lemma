import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetConvergence
open StatMech StatMech.FrontierD


/--
[tendsto_sixVertexCanonicalEvenOffsetNodalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetConvergence.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenOffsetNodalBound_eq
  {c : Real}
  {s : Nat}
  {G : Real}
  {D : NNReal}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalEvenOffsetNodalError c hc s (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeNonperiodicOffsetTestError c (sixVertexFourWidth (2 * s) k) (2 * s) (sixVertexCanonicalFixedEvenDensityFloor hc s) G D) / sixVertexCanonicalOffsetNetMargin c (sixVertexFourWidth (2 * s) k) (2 * s) (sixVertexCanonicalFixedEvenDensityFloor hc s)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenOffsetNodalBound hc s G D

/--
[tendsto_sixVertexCanonicalOddOffsetNodalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetConvergence.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddOffsetNodalBound_eq
  {c : Real}
  {s : Nat}
  {G : Real}
  {D : NNReal}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalOddOffsetNodalError c hc s (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexFixedChargeNonperiodicOffsetTestError c (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) (sixVertexCanonicalFixedOddDensityFloor hc s) G D) / sixVertexCanonicalOffsetNetMargin c (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) (sixVertexCanonicalFixedOddDensityFloor hc s)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddOffsetNodalBound hc s G D

/--
[eventually_uniform_sixVertexCanonicalEvenDensityOffset_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetConvergence.lean)
-/
@[path]
private lemma eventually_uniform_sixVertexCanonicalEvenDensityOffset_fourier_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ k : Nat in atTop, forall i : Fin ((s + k + 1) + (s + k + 1)), := by
-- proof
  apply StatMech.FrontierD.eventually_uniform_sixVertexCanonicalEvenDensityOffset_fourier hc s hepsilon

/--
[eventually_uniform_sixVertexCanonicalOddDensityOffset_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetConvergence.lean)
-/
@[path]
private lemma eventually_uniform_sixVertexCanonicalOddDensityOffset_fourier_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ k : Nat in atTop, forall i : Fin (((s + k + 1) + 1) + (s + k + 1)), := by
-- proof
  apply StatMech.FrontierD.eventually_uniform_sixVertexCanonicalOddDensityOffset_fourier hc s hepsilon


-- created on 2026-10-23
