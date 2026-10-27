import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailCauchy
open StatMech StatMech.FrontierD


/--
[abs_sixVertexFiniteConvolutionDefect_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailCauchy.lean)
-/
@[path]
private lemma abs_sixVertexFiniteConvolutionDefect_le_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  |sixVertexFiniteConvolutionDefect c N (n + 1) p x| <= sixVertexTailConvolutionError c N := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexFiniteConvolutionDefect_le_tail hc htail hN hhalf hopen hsol x

/--
[intervalIntegral_halfFilledFiniteRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailCauchy.lean)
-/
@[path]
private lemma intervalIntegral_halfFilledFiniteRootDensity_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1)) :
-- imply
  ∫ x in -Real.pi..Real.pi, sixVertexFiniteRootDensity c N (n + 1) p x = 1 / 2 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_halfFilledFiniteRootDensity hc hN hhalf p

/--
[sixVertexFiniteRootDensity_weighted_sub_le_of_bound_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailCauchy.lean)
-/
@[path]
private lemma sixVertexFiniteRootDensity_weighted_sub_le_of_bound_tail_eq
  {c : Real}
  {N n M m : Nat}
  {p : Fin (n + 1) → Real}
  {q : Fin (m + 1) → Real}
  {E : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hM : 0 < M)
  (hhalfN : N = 2 * (n + 1))
  (hhalfM : M = 2 * (m + 1))
  (hpopen : SixVertexOpenRootSimplex p)
  (hqopen : SixVertexOpenRootSimplex q)
  (hpsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hqsol : SixVertexSatisfiesBetheEquations c M (m + 1) q)
  (hE : 0 <= E)
  (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c N (n + 1) p y - sixVertexFiniteRootDensity c M (m + 1) q y)| <= E) :
-- imply
  |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N (n + 1) p x - sixVertexFiniteRootDensity c M (m + 1) q x)| <= sixVertexRootDensityContractionRate c * E + (sixVertexTailConvolutionError c N + sixVertexTailConvolutionError c M) / (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteRootDensity_weighted_sub_le_of_bound_tail hc htail hN hM hhalfN hhalfM hpopen hqopen hpsol hqsol hE hbound x

/--
[sixVertexFiniteRootDensity_weighted_cauchy_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailCauchy.lean)
-/
@[path]
private lemma sixVertexFiniteRootDensity_weighted_cauchy_tail_eq
  {c : Real}
  {N n M m : Nat}
  {p : Fin (n + 1) → Real}
  {q : Fin (m + 1) → Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hM : 0 < M)
  (hhalfN : N = 2 * (n + 1))
  (hhalfM : M = 2 * (m + 1))
  (hpopen : SixVertexOpenRootSimplex p)
  (hqopen : SixVertexOpenRootSimplex q)
  (hpsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hqsol : SixVertexSatisfiesBetheEquations c M (m + 1) q) :
-- imply
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N (n + 1) p x - sixVertexFiniteRootDensity c M (m + 1) q x)| <= ((sixVertexTailConvolutionError c N + sixVertexTailConvolutionError c M) / (2 * Real.pi)) / (1 - sixVertexRootDensityContractionRate c) := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteRootDensity_weighted_cauchy_tail hc htail hN hM hhalfN hhalfM hpopen hqopen hpsol hqsol

/--
[sixVertexFiniteRootDensity_weighted_cauchy_of_pos_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailCauchy.lean)
-/
@[path]
private lemma sixVertexFiniteRootDensity_weighted_cauchy_of_pos_tail_eq
  {c : Real}
  {N n M m : Nat}
  {p : Fin n -> Real}
  {q : Fin m -> Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hM : 0 < M)
  (hn : 0 < n)
  (hm : 0 < m)
  (hhalfN : N = 2 * n)
  (hhalfM : M = 2 * m)
  (hpopen : SixVertexOpenRootSimplex p)
  (hqopen : SixVertexOpenRootSimplex q)
  (hpsol : SixVertexSatisfiesBetheEquations c N n p)
  (hqsol : SixVertexSatisfiesBetheEquations c M m q) :
-- imply
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N n p x - sixVertexFiniteRootDensity c M m q x)| <= ((sixVertexTailConvolutionError c N + sixVertexTailConvolutionError c M) / (2 * Real.pi)) / (1 - sixVertexRootDensityContractionRate c) := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteRootDensity_weighted_cauchy_of_pos_tail hc htail hN hM hn hm hhalfN hhalfM hpopen hqopen hpsol hqsol


-- created on 2026-10-23
