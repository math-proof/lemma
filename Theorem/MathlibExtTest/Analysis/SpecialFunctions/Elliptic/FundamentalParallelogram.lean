/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/FundamentalParallelogram.lean -/


import Def.Analysis.SpecialFunctions.Elliptic.FundamentalParallelogram
import Lemma.Complex.FundamentalParallelogram


example (L : PeriodPair) :
    L.fundamentalParallelogram 0 = ZSpan.fundamentalDomain L.basis := by
  simp

example (L : PeriodPair) (α : ℂ) : α ∈ L.fundamentalParallelogram α := by
  rw [PeriodPair.mem_fundamentalParallelogram_iff]
  exact ⟨0, 0, le_rfl, one_pos, le_rfl, one_pos, by simp⟩

example (L : PeriodPair) (α : ℂ) :
    α + (1 / 2 : ℝ) • L.ω₁ + (1 / 2 : ℝ) • L.ω₂ ∈ L.fundamentalParallelogram α := by
  rw [PeriodPair.mem_fundamentalParallelogram_iff]
  exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩

