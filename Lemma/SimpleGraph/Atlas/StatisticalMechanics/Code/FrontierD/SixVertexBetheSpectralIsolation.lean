import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSpectralIsolation
open Finset Filter Matrix Topology StatMech StatMech.FrontierD


/--
[sixVertexHalfFilledBetheCandidateNormalized_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSpectralIsolation.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheCandidateNormalized_ge_eq
  {k : Nat}
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  2 / 2 ^ ((k + 1) + (k + 1)) ≤ sixVertexHalfFilledBetheCandidateNormalized k c := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheCandidateNormalized_ge k hc

/--
[eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSpectralIsolation.lean)
-/
@[path]
private lemma eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top_eq
  {k : Nat}
-- given
  (hnonzero : ∀ᶠ c : Real in atTop, ∀ hc : 2 < c, ∃ a : Complex, sixVertexHalfFilledBetheRotatedRealWave hc k a ≠ 0) :
-- imply
  ∀ᶠ c : Real in atTop, sixVertexHalfFilledBetheCandidateNormalized k c = sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by unfold sixVertexFourWidth omega) c / (c ^ 2 - 2) ^ ((k + 1) + (k + 1)) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top k hnonzero


-- created on 2026-10-23
