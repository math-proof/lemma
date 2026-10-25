import Mathlib
import Theorem.Analysis.Section_5_1.Part9
import Theorem.Analysis.Section_5_3.Part12
import Theorem.Analysis.Section_5_epilogue.Part5
import Abbrev.Analysis.Section_6_1.Part6


/-- Definition 6.1.3 (Eventually ε-steady, def) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) := by rfl

/-- For fixed {name}`a`, the function `ε ↦ ε.Steady s` is monotone -/
theorem Real.Steady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂) (hsteady: ε₁.Steady a) :
    ε₂.Steady a := by grind

/-- For fixed {name}`a`, the function `ε ↦ ε.EventuallySteady s` is monotone -/
theorem Real.EventuallySteady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.EventuallySteady a) :
    ε₂.EventuallySteady a := by peel 2 hsteady; grind [Steady.mono]

