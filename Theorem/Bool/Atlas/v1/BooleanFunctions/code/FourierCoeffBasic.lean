module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Parseval
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
public import Def.v1.Atlas.BooleanFunctions.code.Parseval
public import Def.v1.Atlas.BooleanFunctions.code.InfluenceFourier
public import Def.v1.Atlas.BooleanFunctions.code.Stability
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.NoiseStability
open Finset BigOperators


public section

namespace BooleanFourier

/--
[noiseOp_preserves_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierCoeffBasic.lean)
-/
@[path]
theorem noiseOp_preserves_expectation
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
