import Mathlib
import sympy.Basic
import Structure.v1.Atlas.TheoryOfProbability.code.Blumenthal01
open MeasureTheory MeasurableSpace Filtration ProbabilityTheory


namespace ProbabilityTheory

/--
[germSigmaAlgebraZero_eq_iInf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Blumenthal01.lean)
-/
@[path]
lemma germSigmaAlgebraZero_eq_iInf
  {m : MeasurableSpace Ω}
  {𝓕 : Filtration NNReal m} :
-- imply
  germSigmaAlgebraZero 𝓕 = ⨅ t > (0 : NNReal), 𝓕 t :=
-- proof
  rfl

end ProbabilityTheory

namespace ProbabilityTheory

/--
[germSigmaAlgebraZero_le_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Blumenthal01.lean)
-/
@[path]
lemma germSigmaAlgebraZero_le_of_pos
  {m : MeasurableSpace Ω}
  {𝓕 : Filtration NNReal m}
  {t : NNReal}
-- given
  (ht : 0 < t) :
-- imply
  germSigmaAlgebraZero 𝓕 ≤ 𝓕 t := by
-- proof
  rw [germSigmaAlgebraZero_eq_iInf]
  exact iInf₂_le t ht
/-- For Brownian motion, every component `𝓕 s` of the filtration (with `s > 0`)
is independent of the germ σ-algebra at `0`. This is a Markov-property
consequence of the independent-increments property and is the main ingredient
in the proof of Blumenthal's 0-1 law. -/

end ProbabilityTheory


-- created on 2026-10-23
