import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.BilinearForm.Prod
open LinearMap (BilinForm)
open Module
open LinearMap
open BilinForm


/--
[prod_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/Prod.lean)
-/
@[path]
private lemma prod_apply_eq
  [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  {B₁ : BilinForm R M₁}
  {B₂ : BilinForm R M₂}
  {x y : M₁ × M₂} :
-- imply
  B₁.prod B₂ x y = B₁ x.1 y.1 + B₂ x.2 y.2 := by
-- proof
  apply LinearMap.BilinForm.prod_apply B₁ B₂ x y

/--
[nondegenerate_prod_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/Prod.lean)
-/
@[path]
private lemma nondegenerate_prod_iff_eq
  [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  {B₁ : BilinForm R M₁}
  {B₂ : BilinForm R M₂} :
-- imply
  (B₁.prod B₂).Nondegenerate ↔ B₁.Nondegenerate ∧ B₂.Nondegenerate := by
-- proof
  apply LinearMap.BilinForm.nondegenerate_prod_iff

/--
[dualSubmodule_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/Prod.lean)
-/
@[path]
private lemma dualSubmodule_prod_eq
  [CommRing R] [Field S] [AddCommGroup M₁] [AddCommGroup M₂] [Algebra R S] [Module R M₁] [Module R M₂] [Module S M₁] [Module S M₂] [IsScalarTower R S M₁] [IsScalarTower R S M₂]
  {B₁ : BilinForm S M₁}
  {B₂ : BilinForm S M₂}
  {N₁ : Submodule R M₁}
  {N₂ : Submodule R M₂} :
-- imply
  (B₁.prod B₂).dualSubmodule (N₁.prod N₂) =
    (B₁.dualSubmodule N₁).prod (B₂.dualSubmodule N₂) := by
-- proof
  apply LinearMap.BilinForm.dualSubmodule_prod B₁ B₂ N₁ N₂


-- created on 2026-10-20
