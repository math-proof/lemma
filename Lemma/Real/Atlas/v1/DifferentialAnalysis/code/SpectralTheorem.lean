import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SpectralTheorem
open SpectralTheorem
open scoped ComplexInnerProductSpace


namespace SpectralTheorem

/--
[spectrum_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SpectralTheorem.lean)
-/
@[path]
lemma spectrum_isCompact
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {T : H →L[ℂ] H} :
-- imply
  IsCompact (spectrum ℂ T) :=
-- proof
  spectrum.isCompact T

end SpectralTheorem

namespace SpectralTheorem

/--
[spectrum_subset_closedBall_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SpectralTheorem.lean)
-/
@[path]
lemma spectrum_subset_closedBall_norm
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [NontrivialTopology H]
  {T : H →L[ℂ] H} :
-- imply
  spectrum ℂ T ⊆ Metric.closedBall (0 : ℂ) ‖T‖ :=
-- proof
  spectrum.subset_closedBall_norm T

end SpectralTheorem

namespace SpectralTheorem

/--
[spectrum_compact_subset_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SpectralTheorem.lean)
-/
@[path]
lemma spectrum_compact_subset_closedBall
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [NontrivialTopology H]
  {T : H →L[ℂ] H} :
-- imply
  IsCompact (spectrum ℂ T) ∧ spectrum ℂ T ⊆ Metric.closedBall (0 : ℂ) ‖T‖ :=
-- proof
  ⟨spectrum_isCompact T, spectrum_subset_closedBall_norm T⟩

end SpectralTheorem

namespace SpectralTheorem

/--
[norm_polynomial_selfAdjoint_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SpectralTheorem.lean)
-/
@[path]
lemma norm_polynomial_selfAdjoint_le
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {A : H →L[ℂ] H}
  {q : ℝ[X]}
  {c : ℝ}
-- given
  (hA : IsSelfAdjoint A)
  (hc : 0 ≤ c)
  (hbound : ∀ t ∈ spectrum ℝ A, ‖eval t q‖ ≤ c) :
-- imply
  ‖aeval A q‖ ≤ c := by
-- proof
  rw [← cfc_polynomial q A hA]
  exact norm_cfc_le hc hbound

end SpectralTheorem

namespace SpectralTheorem

/--
[norm_polynomial_selfAdjoint_le_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SpectralTheorem.lean)
-/
@[path]
lemma norm_polynomial_selfAdjoint_le_Icc
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {A : H →L[ℂ] H}
  {q : ℝ[X]}
  {m M : ℝ}
  {c : ℝ}
-- given
  (hA : IsSelfAdjoint A)
  (hspec : spectrum ℝ A ⊆ Set.Icc m M)
  (hc : 0 ≤ c)
  (hbound : ∀ t ∈ Set.Icc m M, ‖eval t q‖ ≤ c) :
-- imply
  ‖aeval A q‖ ≤ c :=
-- proof
  norm_polynomial_selfAdjoint_le A hA q hc fun t ht => hbound t (hspec ht)
end SpectralTheorem



-- created on 2026-10-23
