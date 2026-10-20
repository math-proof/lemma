import Mathlib
import sympy.Basic
import sympy.atlas.Probability.KolmogorovExtension
open MeasureTheory
open scoped ENNReal
open MathlibExt.Probability.KolmogorovExtensionWanted


/--
[kolmogorov_extension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/KolmogorovExtension.lean)
-/
@[path]
private lemma kolmogorov_extension_eq
  [∀ J, IsProbabilityMeasure (P J)]
  {α : ι → Type*} [∀ i, TopologicalSpace (α i)] [∀ i, PolishSpace (α i)] [∀ i, MeasurableSpace (α i)] [∀ i, BorelSpace (α i)]
-- given
  (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
  (hP : IsProjectiveMeasureFamily P) :
-- imply
  ∃ μ : Measure (∀ i, α i), IsProjectiveLimit μ P := by
-- proof
  apply MathlibExt.Probability.KolmogorovExtensionWanted.kolmogorov_extension P hP


-- created on 2026-10-20
