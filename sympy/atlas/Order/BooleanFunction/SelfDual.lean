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

@[simp]
theorem booleanFunctionDual_apply (n : Nat) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    booleanFunctionDual n f x = !(f (booleanVectorComplement n x)) :=
  rfl

/-- Complementing a Boolean vector twice returns the original vector. -/
@[simp]
theorem booleanVectorComplement_complement (n : Nat) (x : Fin n → Bool) :
    booleanVectorComplement n (booleanVectorComplement n x) = x := by
  funext i
  simp [booleanVectorComplement]

/-- Boolean-function duality is involutive. -/
@[simp]
theorem booleanFunctionDual_dual (n : Nat) (f : (Fin n → Bool) → Bool) :
    booleanFunctionDual n (booleanFunctionDual n f) = f := by
  funext x
  simp [booleanFunctionDual]

/-- Every coordinate projection is a self-dual monotone Boolean function. -/
theorem selfDualMonotone_proj {n : Nat} (i : Fin n) :
    IsSelfDualMonotone n (fun x : Fin n → Bool => x i) := by
  refine ⟨fun x y h => h i, ?_⟩
  funext x
  simp [booleanFunctionDual, booleanVectorComplement]

end MetaMathlibExt
