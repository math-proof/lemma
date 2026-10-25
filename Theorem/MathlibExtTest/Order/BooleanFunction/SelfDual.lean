/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/BooleanFunction/SelfDual.lean -/


import Def.Order.BooleanFunction.SelfDual
import Lemma.Set.BooleanFunction.SelfDual


namespace MetaMathlibExt

/-- At `n = 0` there is no self-dual Boolean function: the unique input is
fixed by complement, so self-duality would force `b = !b`. -/
example : ¬∃ f : (Fin 0 → Bool) → Bool, IsSelfDualMonotone 0 f := by
  rintro ⟨f, _, heq⟩
  let x : Fin 0 → Bool := fun i => Fin.elim0 i
  have hcompl : booleanVectorComplement 0 x = x := by
    funext i
    exact Fin.elim0 i
  have h1 : f x = booleanFunctionDual 0 f x := congrArg (fun g => g x) heq
  rw [booleanFunctionDual_apply, hcompl] at h1
  have hne : f x ≠ !(f x) := by
    cases hfx : f x <;> decide
  exact hne h1

example : IsSelfDualMonotone 1 (fun x : Fin 1 → Bool => x 0) :=
  selfDualMonotone_proj 0

example : IsSelfDualMonotone 2 (fun x : Fin 2 → Bool => x 0) :=
  selfDualMonotone_proj 0

example : IsSelfDualMonotone 2 (fun x : Fin 2 → Bool => x 1) :=
  selfDualMonotone_proj 1

end MetaMathlibExt
