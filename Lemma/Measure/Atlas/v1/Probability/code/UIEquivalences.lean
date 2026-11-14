import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.Probability.code.UIEquivalences
open MeasureTheory TheoryOfProbability3
open scoped MeasureTheory NNReal ENNReal


namespace TheoryOfProbability3

/--
[textbookUI'_iff_uniformIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIEquivalences.lean)
-/
@[path]
lemma textbookUI'_iff_uniformIntegrable
  {m : MeasurableSpace α}
  {μ : Measure α}
  [IsFiniteMeasure μ]
  {f : ι → α → ℝ} :
-- imply
  TextbookUniformlyIntegrable' f μ ↔ UniformIntegrable f 1 μ := by
-- proof
  rw [uniformIntegrable_iff le_rfl ENNReal.one_ne_top]
  constructor
  · rintro ⟨hmeas, htail⟩
    refine ⟨hmeas, ?_⟩
    intro ε hε
    by_cases htop : ε = ∞
    · exact ⟨0, fun _ => htop ▸ le_top⟩
    · have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
      obtain ⟨C, hC⟩ := htail ε.toReal hεr
      exact ⟨C, fun i => (hC i).trans ENNReal.ofReal_toReal_le⟩
  · rintro ⟨hmeas, htail⟩
    refine ⟨hmeas, ?_⟩
    intro ε hε
    exact htail (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[textbookUI_iff_bound_and_unifAbsCont](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIEquivalences.lean)
-/
@[path]
lemma textbookUI_iff_bound_and_unifAbsCont
  {m : MeasurableSpace α}
  {μ : Measure α}
  [IsFiniteMeasure μ]
  {f : ι → α → ℝ} :
-- imply
  TextbookUniformlyIntegrable' f μ ↔ (∀ i, AEStronglyMeasurable (f i) μ) ∧ UnifAbsContIntegrals f μ ∧ UnifL1Bound f μ := by
-- proof
  rw [textbookUI'_iff_uniformIntegrable]
  constructor
  · intro h
    exact ⟨h.aestronglyMeasurable, h.1, h.2⟩
  · rintro ⟨_, hU, hB⟩
    exact ⟨hU, hB⟩

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[TextbookUniformlyIntegrable'.unifL1Bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIEquivalences.lean)
-/
@[path]
lemma TextbookUniformlyIntegrable'.unifL1Bound
  {m : MeasurableSpace α}
  {μ : Measure α}
  [IsFiniteMeasure μ]
  {f : ι → α → ℝ}
-- given
  (hf : TextbookUniformlyIntegrable' f μ) :
-- imply
  UnifL1Bound f μ :=
-- proof
  (textbookUI_iff_bound_and_unifAbsCont.mp hf).2.2

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[TextbookUniformlyIntegrable'.unifAbsContIntegrals](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIEquivalences.lean)
-/
@[path]
lemma TextbookUniformlyIntegrable'.unifAbsContIntegrals
  {m : MeasurableSpace α}
  {μ : Measure α}
  [IsFiniteMeasure μ]
  {f : ι → α → ℝ}
-- given
  (hf : TextbookUniformlyIntegrable' f μ) :
-- imply
  UnifAbsContIntegrals f μ :=
-- proof
  (textbookUI_iff_bound_and_unifAbsCont.mp hf).2.1

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[TextbookUniformlyIntegrable'.aEStronglyMeasurable'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIEquivalences.lean)
-/
@[path]
lemma TextbookUniformlyIntegrable'.aEStronglyMeasurable'
  {m : MeasurableSpace α}
  {μ : Measure α}
  [IsFiniteMeasure μ]
  {f : ι → α → ℝ}
-- given
  (hf : TextbookUniformlyIntegrable' f μ) :
-- imply
  ∀ i, AEStronglyMeasurable (f i) μ :=
-- proof
  (textbookUI_iff_bound_and_unifAbsCont.mp hf).1

end TheoryOfProbability3


-- created on 2026-10-23
