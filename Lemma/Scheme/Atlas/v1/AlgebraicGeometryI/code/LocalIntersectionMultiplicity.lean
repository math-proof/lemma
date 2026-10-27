import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.LocalIntersectionMultiplicity
open MvPolynomial Module LocalIntersection


namespace LocalIntersection

/--
[mulByXOp_mul_mulByYOp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocalIntersectionMultiplicity.lean)
-/
@[path]
lemma mulByXOp_mul_mulByYOp
  {k : Type*}
  [Field k]
  {f g : MvPolynomial (Fin 2) k} :
-- imply
  mulByXOp k f g * mulByYOp k f g = mulByYOp k f g * mulByXOp k f g := by
-- proof
  unfold mulByXOp mulByYOp
  simp only [← map_mul (Algebra.lmul k _)]
  exact congr_arg _ (mul_comm _ _)

end LocalIntersection

namespace LocalIntersection

/--
[localIntersectionMultiplicity_eq_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocalIntersectionMultiplicity.lean)
-/
@[path]
lemma localIntersectionMultiplicity_eq_finrank
  {k : Type*}
  [Field k]
  {f g : MvPolynomial (Fin 2) k}
  {a b : k} :
-- imply
  localIntersectionMultiplicity k f g a b = finrank k ↥((mulByXOp k f g).maxGenEigenspace a ⊓ (mulByYOp k f g).maxGenEigenspace b) := by
-- proof
  rfl
end LocalIntersection



-- created on 2026-10-23
