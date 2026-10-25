/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/BooleanFunction/SelfDual.lean -/

import Mathlib.Data.Bool.Basic


namespace MetaMathlibExt

/-- Coordinatewise complement on a Boolean vector.

Concept `jis_term_d4ca78498f0fce5b71d05655`; source JIS VOL28/Pawelski,
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Pawelski/pawelski22.tex>, lines 72–81. -/
def booleanVectorComplement (n : Nat) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => !(x i)

/-- The dual Boolean function `f⋆ x = !(f (xᶜ))`. -/
def booleanFunctionDual (n : Nat) (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => !(f (booleanVectorComplement n x))

/-- A self-dual monotone Boolean function: a coordinatewise monotone function
equal to its dual. -/
def IsSelfDualMonotone (n : Nat) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ x y : Fin n → Bool, (∀ i, x i ≤ y i) → f x ≤ f y) ∧ f = booleanFunctionDual n f

end MetaMathlibExt
