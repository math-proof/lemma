import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Order.BooleanFunction.SelfDual
open MetaMathlibExt


namespace MetaMathlibExt

/--
[booleanFunctionDual_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/BooleanFunction/SelfDual.lean)
-/
@[path]
lemma booleanFunctionDual_apply
  {n : Nat}
  {f : (Fin n → Bool) → Bool}
  {x : Fin n → Bool} :
-- imply
  booleanFunctionDual n f x = !(f (booleanVectorComplement n x)) :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[booleanVectorComplement_complement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/BooleanFunction/SelfDual.lean)
-/
@[path]
lemma booleanVectorComplement_complement
  {n : Nat}
  {x : Fin n → Bool} :
-- imply
  booleanVectorComplement n (booleanVectorComplement n x) = x := by
-- proof
  funext i
  simp [booleanVectorComplement]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[booleanFunctionDual_dual](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/BooleanFunction/SelfDual.lean)
-/
@[path]
lemma booleanFunctionDual_dual
  {n : Nat}
  {f : (Fin n → Bool) → Bool} :
-- imply
  booleanFunctionDual n (booleanFunctionDual n f) = f := by
-- proof
  funext x
  simp [booleanFunctionDual]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[selfDualMonotone_proj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/BooleanFunction/SelfDual.lean)
-/
@[path]
lemma selfDualMonotone_proj
  {n : Nat}
  {i : Fin n} :
-- imply
  IsSelfDualMonotone n (fun x : Fin n → Bool => x i) := by
-- proof
  refine ⟨fun x y h => h i, ?_⟩
  funext x
  simp [booleanFunctionDual, booleanVectorComplement]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
