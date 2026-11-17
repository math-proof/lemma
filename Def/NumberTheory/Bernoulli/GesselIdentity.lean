/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/GesselIdentity.lean -/

module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false


section

namespace MetaMathlibExt

noncomputable def myL : Polynomial ℚ →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun n : ℕ => (_root_.bernoulli n) • LinearMap.id)

end MetaMathlibExt
end
