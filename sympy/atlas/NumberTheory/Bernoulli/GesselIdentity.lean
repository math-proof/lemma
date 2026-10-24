/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/GesselIdentity.lean -/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

section
namespace MetaMathlibExt

private noncomputable def myL : Polynomial ℚ →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun n : ℕ => (_root_.bernoulli n) • LinearMap.id)
end MetaMathlibExt
end
