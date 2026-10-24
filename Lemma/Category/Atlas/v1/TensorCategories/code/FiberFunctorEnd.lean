import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.FiberFunctorEnd
open TensorProduct


namespace FiberFunctorEnd

/--
[endTensorEndAlgHom_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiberFunctorEnd.lean)
-/
@[path]
lemma endTensorEndAlgHom_tmul
  {φ : Module.End k M}
  {ψ : Module.End k N} :
-- imply
  endTensorEndAlgHom k M N (φ ⊗ₜ ψ) = TensorProduct.map φ ψ := by
-- proof
  simp only [endTensorEndAlgHom, Algebra.TensorProduct.lift_tmul]
  ext m n
  simp [Module.End.rTensorAlgHom, Module.End.lTensorAlgHom,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul]
variable [Module.Free k M] [Module.Finite k M]
  [Module.Free k N] [Module.Finite k N]

end FiberFunctorEnd

namespace FiberFunctorEnd

/--
[endTensorEndAlgEquiv_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiberFunctorEnd.lean)
-/
@[path]
lemma endTensorEndAlgEquiv_tmul
  [Module.Free k M]
  [Module.Finite k M]
  {φ : Module.End k M}
  {ψ : Module.End k N} :
-- imply
  endTensorEndAlgEquiv k M N (φ ⊗ₜ ψ) = TensorProduct.map φ ψ := by
-- proof
  simp [endTensorEndAlgEquiv, homTensorHomMap_apply]

end FiberFunctorEnd

/--
[rTensor_lTensor_commute](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiberFunctorEnd.lean)
-/
@[path]
private lemma rTensor_lTensor_commute_eq
  {φ : Module.End k M}
  {ψ : Module.End k N} :
-- imply
  Commute (Module.End.rTensorAlgHom k M N φ) (Module.End.lTensorAlgHom k N M ψ) := by
-- proof
  apply rTensor_lTensor_commute φ ψ


-- created on 2026-10-23
