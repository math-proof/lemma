import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.Hypercontractivity
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Hypercontractivity
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Stability
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.TwoPointInequality
import Def.v1.Atlas.BooleanFunctions.code.Stability
import Def.v1.Atlas.BooleanFunctions.code.TwoPointInequality
open Finset BigOperators Real


namespace BooleanFourier

/--
[lpNorm_noiseOperator_le_of_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/HypercontractivityThm.lean)
-/
@[path]
lemma lpNorm_noiseOperator_le_of_twoPoint
  {n : ℕ}
  {f : BoolFn n}
  {p q ρ : ℝ}
-- given
  (hp : 1 ≤ p)
  (hpq : p ≤ q)
  (hρ_nonneg : 0 ≤ ρ)
  (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (q - 1)))
  (_h_twopoint : ∀ (g : Bool → ℝ), twoPointLpNorm q (twoPointNoiseOp ρ g) ≤ twoPointLpNorm p g) :
-- imply
  lpNorm q (noiseOperator ρ f) ≤ lpNorm p f :=
-- proof
bonami_beckner f hp hpq hρ_nonneg hρ_bound

end BooleanFourier

namespace BooleanFourier

/--
[hypercontractivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/HypercontractivityThm.lean)
-/
@[path]
lemma hypercontractivity
  {n : ℕ}
  {f : BoolFn n}
  {p q ρ : ℝ}
-- given
  (hp : 1 ≤ p)
  (hpq : p ≤ q)
  (hρ_nonneg : 0 ≤ ρ)
  (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (q - 1))) :
-- imply
  lpNorm q (noiseOperator ρ f) ≤ lpNorm p f :=
-- proof
  lpNorm_noiseOperator_le_of_twoPoint f hp hpq hρ_nonneg hρ_bound
    (fun g => two_point_inequality hp hpq hρ_nonneg hρ_bound g)

end BooleanFourier


-- created on 2026-10-23
