import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Filter


/--
[fatou_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/FatouLemma.lean)
-/
@[path]
lemma fatou_lemma
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
-- given
  (hf : ∀ n, Measurable (f n)) :
-- imply
  ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
-- proof
  MeasureTheory.lintegral_liminf_le hf

/--
[fatou_lemma'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/FatouLemma.lean)
-/
@[path]
lemma fatou_lemma'
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
-- given
  (hf : ∀ n, AEMeasurable (f n) μ) :
-- imply
  ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
-- proof
  MeasureTheory.lintegral_liminf_le' hf


-- created on 2026-10-23
