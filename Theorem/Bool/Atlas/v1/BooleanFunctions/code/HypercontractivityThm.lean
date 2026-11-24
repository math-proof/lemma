module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.BooleanFunctions.code.Hypercontractivity
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Hypercontractivity
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Stability
public import Lemma.Bool.Atlas.v1.BooleanFunctions.code.TwoPointInequality
public import Def.v1.Atlas.BooleanFunctions.code.Stability
public import Def.v1.Atlas.BooleanFunctions.code.TwoPointInequality
open Finset BigOperators Real


public section

namespace BooleanFourier

/--
[lpNorm_noiseOperator_le_of_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/HypercontractivityThm.lean)
-/
theorem lpNorm_noiseOperator_le_of_twoPoint
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
theorem hypercontractivity
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
-- updated on 2026-11-24
