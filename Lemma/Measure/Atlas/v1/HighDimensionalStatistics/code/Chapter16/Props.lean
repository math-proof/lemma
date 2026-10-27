import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter16.Props
open Metric Set


/--
[prop_16_1_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter16/Props.lean)
-/
@[path]
lemma prop_16_1_isCompact
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [Nontrivial H]
  {T : H →L[ℂ] H} :
-- imply
  IsCompact (spectrum ℂ T) :=
-- proof
  spectrum.isCompact T

/--
[prop_16_1_subset_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter16/Props.lean)
-/
@[path]
lemma prop_16_1_subset_closedBall
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [Nontrivial H]
  {T : H →L[ℂ] H} :
-- imply
  spectrum ℂ T ⊆ closedBall 0 ‖T‖ := by
-- proof
  intro k hk
  simp only [mem_closedBall, dist_zero_right]
  exact spectrum.norm_le_norm_of_mem hk

/--
[prop_16_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter16/Props.lean)
-/
@[path]
lemma prop_16_1
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [Nontrivial H]
  {T : H →L[ℂ] H} :
-- imply
  IsCompact (spectrum ℂ T) ∧ spectrum ℂ T ⊆ closedBall 0 ‖T‖ :=
-- proof
  ⟨prop_16_1_isCompact T, prop_16_1_subset_closedBall T⟩
/-- Proposition 16.2: for a self-adjoint operator `A`, both endpoints of the
numerical range `m, M` lie in the spectrum, and the spectrum is real and
contained in the real interval `[m, M]`. -/


-- created on 2026-10-23
