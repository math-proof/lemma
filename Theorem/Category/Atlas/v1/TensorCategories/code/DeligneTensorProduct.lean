module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.TensorCategories.code.DeligneTensorProduct.Part3
public section

open TensorProduct CategoryTheory ModuleCat Deligne


namespace Deligne

/--
[boxtimesMap_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProduct.lean)
-/
public theorem boxtimesMap_tmul
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
  [IsScalarTower k A M₁]
  [SMulCommClass k A M₁]
  {N₁ : Type}
  [AddCommGroup N₁]
  [Module k N₁]
  [Module B N₁]
  [IsScalarTower k B N₁]
  [SMulCommClass k B N₁]
  {M₂ : Type}
  [AddCommGroup M₂]
  [Module k M₂]
  [Module A M₂]
  [IsScalarTower k A M₂]
  [SMulCommClass k A M₂]
  {N₂ : Type}
  [AddCommGroup N₂]
  [Module k N₂]
  [Module B N₂]
  [IsScalarTower k B N₂]
  [SMulCommClass k B N₂]
  {f : M₁ →ₗ[A] M₂}
  {g : N₁ →ₗ[B] N₂}
  {m : M₁}
  {n : N₁} :
-- imply
  boxtimesMap k A B M₁ N₁ M₂ N₂ f g (m ⊗ₜ[k] n) = (f m) ⊗ₜ[k] (g n) := by
-- proof
  simp [boxtimesMap, TensorProduct.map_tmul, LinearMap.restrictScalars_apply]
end Deligne

/--
[actA_actB_commute](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProduct.lean)
-/
public theorem actA_actB_commute_eq
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
  [IsScalarTower k A M]
  [SMulCommClass k A M]
  {N : Type}
  [AddCommGroup N]
  [Module k N]
  [Module B N]
  [IsScalarTower k B N]
  [SMulCommClass k B N]
  {a : A}
  {b : B} :
-- imply
  Commute (actA k A M N a) (actB k B M N b) := by
-- proof
  apply Deligne.actA_actB_commute k A B M N a b

/--
[actAB_tmul_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProduct.lean)
-/
public theorem actAB_tmul_tmul_eq
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
  [IsScalarTower k A M]
  [SMulCommClass k A M]
  {N : Type}
  [AddCommGroup N]
  [Module k N]
  [Module B N]
  [IsScalarTower k B N]
  [SMulCommClass k B N]
  {a : A}
  {b : B}
  {m : M}
  {n : N} :
-- imply
  actAB k A B M N (a ⊗ₜ[k] b) (m ⊗ₜ[k] n) = (a • m) ⊗ₜ[k] (b • n) := by
-- proof
  apply Deligne.actAB_tmul_tmul k A B M N a b m n


-- created on 2026-10-23
