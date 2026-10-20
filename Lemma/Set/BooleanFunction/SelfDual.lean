import Mathlib
import sympy.Basic
import sympy.atlas.Order.BooleanFunction.SelfDual
open MetaMathlibExt


/--
[booleanFunctionDual_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/BooleanFunction/SelfDual.lean)
-/
@[path]
private lemma booleanFunctionDual_apply_eq
  {n : Nat}
  {f : (Fin n → Bool) → Bool}
  {x : Fin n → Bool} :
-- imply
  booleanFunctionDual n f x = !(f (booleanVectorComplement n x)) := by
-- proof
  apply MetaMathlibExt.booleanFunctionDual_apply n f x

/--
[booleanVectorComplement_complement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/BooleanFunction/SelfDual.lean)
-/
@[path]
private lemma booleanVectorComplement_complement_eq
  {n : Nat}
  {x : Fin n → Bool} :
-- imply
  booleanVectorComplement n (booleanVectorComplement n x) = x := by
-- proof
  apply MetaMathlibExt.booleanVectorComplement_complement n x

/--
[booleanFunctionDual_dual](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/BooleanFunction/SelfDual.lean)
-/
@[path]
private lemma booleanFunctionDual_dual_eq
  {n : Nat}
  {f : (Fin n → Bool) → Bool} :
-- imply
  booleanFunctionDual n (booleanFunctionDual n f) = f := by
-- proof
  apply MetaMathlibExt.booleanFunctionDual_dual n f

/--
[selfDualMonotone_proj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/BooleanFunction/SelfDual.lean)
-/
@[path]
private lemma selfDualMonotone_proj_eq
  {n : Nat}
  {i : Fin n} :
-- imply
  IsSelfDualMonotone n (fun x : Fin n → Bool => x i) := by
-- proof
  apply MetaMathlibExt.selfDualMonotone_proj i


-- created on 2026-10-20
