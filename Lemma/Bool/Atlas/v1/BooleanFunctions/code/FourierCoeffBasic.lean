import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Parseval
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
import Def.v1.Atlas.BooleanFunctions.code.Parseval
import Def.v1.Atlas.BooleanFunctions.code.InfluenceFourier
open Finset BigOperators


namespace BooleanFourier

/--
[noiseOp_preserves_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierCoeffBasic.lean)
-/
@[path]
lemma noiseOp_preserves_expectation
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  fourierCoeff (noiseOperator ρ f) ∅ = fourierCoeff f ∅ := by
-- proof
  rw [fourierCoeff_noiseOperator]
  simp [Finset.card_empty]

end BooleanFourier


-- created on 2026-10-23
