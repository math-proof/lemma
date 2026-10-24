import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.DeligneTensorProduct
open TensorProduct CategoryTheory ModuleCat Deligne


namespace Deligne

/--
[boxtimesMap_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProduct.lean)
-/
@[path]
lemma boxtimesMap_tmul
  {k : Type}
  [CommRing k]
  {A : Type}
  [Ring A]
  [Algebra k A]
  {B : Type}
  [Ring B]
  [Algebra k B]
  {M₁ : Type}
  [AddCommGroup M₁]
  [Module k M₁]
  [Module A M₁]
  {N₁ : Type}
  [AddCommGroup N₁]
  [Module k N₁]
  [Module B N₁]
  {M₂ : Type}
  [AddCommGroup M₂]
  [Module k M₂]
  [Module A M₂]
  {N₂ : Type}
  [AddCommGroup N₂]
  [Module k N₂]
  [Module B N₂]
  {f : M₁ →ₗ[A] M₂}
  {g : N₁ →ₗ[B] N₂}
  {m : M₁}
  {n : N₁} :
-- imply
  boxtimesMap k A B M₁ N₁ M₂ N₂ f g (m ⊗ₜ[k] n) = (f m) ⊗ₜ[k] (g n) := by
-- proof
  simp [boxtimesMap, TensorProduct.map_tmul, LinearMap.restrictScalars_apply]
variable (M₃ : Type) [AddCommGroup M₃] [Module k M₃] [Module A M₃]
  [IsScalarTower k A M₃] [SMulCommClass k A M₃]
variable (N₃ : Type) [AddCommGroup N₃] [Module k N₃] [Module B N₃]
  [IsScalarTower k B N₃] [SMulCommClass k B N₃]
section HomMap
variable (A : Type) [Ring A] [Algebra k A]
variable (B : Type) [Ring B] [Algebra k B]
variable (M₁ N₁ : Type) [AddCommGroup M₁] [Module k M₁] [Module A M₁]
  [IsScalarTower k A M₁]
  [AddCommGroup N₁] [Module k N₁] [Module A N₁]
  [IsScalarTower k A N₁] [SMulCommClass k A N₁]
variable (M₂ N₂ : Type) [AddCommGroup M₂] [Module k M₂] [Module B M₂]
  [IsScalarTower k B M₂]
  [AddCommGroup N₂] [Module k N₂] [Module B N₂]
  [IsScalarTower k B N₂] [SMulCommClass k B N₂]

end Deligne

/--
[actA_actB_commute](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProduct.lean)
-/
@[path]
private lemma actA_actB_commute_eq
  {k : Type}
  [CommRing k]
  {A : Type}
  [Ring A]
  [Algebra k A]
  {B : Type}
  [Ring B]
  [Algebra k B]
  {M : Type}
  [AddCommGroup M]
  [Module k M]
  [Module A M]
  {N : Type}
  [AddCommGroup N]
  [Module k N]
  [Module B N]
  {a : A}
  {b : B} :
-- imply
  Commute (actA k A M N a) (actB k B M N b) := by
-- proof
  apply Deligne.actA_actB_commute k A B M N a b

/--
[actAB_tmul_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProduct.lean)
-/
@[path]
private lemma actAB_tmul_tmul_eq
  {k : Type}
  [CommRing k]
  {A : Type}
  [Ring A]
  [Algebra k A]
  {B : Type}
  [Ring B]
  [Algebra k B]
  {M : Type}
  [AddCommGroup M]
  [Module k M]
  [Module A M]
  {N : Type}
  [AddCommGroup N]
  [Module k N]
  [Module B N]
  {a : A}
  {b : B}
  {m : M}
  {n : N} :
-- imply
  actAB k A B M N (a ⊗ₜ[k] b) (m ⊗ₜ[k] n) = (a • m) ⊗ₜ[k] (b • n) := by
-- proof
  apply Deligne.actAB_tmul_tmul k A B M N a b m n


-- created on 2026-10-23
