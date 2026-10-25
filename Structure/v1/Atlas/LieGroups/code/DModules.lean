/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Derivation.Lie
import Def.v1.Atlas.LieGroups.code.DModules
universe u v w


namespace DModules

open scoped TensorProduct

section DModulesAffine

structure LeftDModule (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
    (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] where
  vecFieldAction : Derivation k A A → M →ₗ[k] M
  vecFieldAction_smul : ∀ (v : Derivation k A A) (f : A) (m : M),
    vecFieldAction v (f • m) = f • vecFieldAction v m + v f • m
  vecFieldAction_smul_vec : ∀ (f : A) (v : Derivation k A A) (m : M),
    vecFieldAction (f • v) m = f • vecFieldAction v m
  vecFieldAction_lie : ∀ (v w : Derivation k A A) (m : M),
    vecFieldAction v (vecFieldAction w m) - vecFieldAction w (vecFieldAction v m) =
      vecFieldAction ⁅v, w⁆ m

structure RightDModule (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
    (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] where
  vecFieldAction : Derivation k A A → M →ₗ[k] M
  right_leibniz : ∀ (v : Derivation k A A) (f : A) (m : M),
    vecFieldAction v (f • m) = f • vecFieldAction v m - v f • m
  lin_in_vec : ∀ (f : A) (v : Derivation k A A) (m : M),
    vecFieldAction (f • v) m = f • vecFieldAction v m
  flat : ∀ (v w : Derivation k A A) (m : M),
    vecFieldAction v (vecFieldAction w m) - vecFieldAction w (vecFieldAction v m) =
      - vecFieldAction ⁅v, w⁆ m

end DModulesAffine

section DModulesSheaf

structure SheafOfDiffOps (k : Type u) [CommRing k] where
  I : Type v
  coordRing : I → Type w
  instCommRing : ∀ i, CommRing (coordRing i)
  instAlgebra : ∀ i, Algebra k (coordRing i)
  diffOpsRing : I → Type w
  instDiffRing : ∀ i, Ring (diffOpsRing i)
  instDiffAlgebra : ∀ i, @Algebra (coordRing i) (diffOpsRing i)
    (instCommRing i).toCommSemiring (instDiffRing i).toSemiring
  incl : I → I → Prop
  incl_refl : ∀ i, incl i i
  incl_trans : ∀ {i j k}, incl i j → incl j k → incl i k
  coordRestrict : ∀ {i j}, incl i j →
    @RingHom (coordRing i) (coordRing j)
      (instCommRing i).toNonAssocSemiring (instCommRing j).toNonAssocSemiring
  diffOpsRestrict : ∀ {i j}, incl i j →
    @RingHom (diffOpsRing i) (diffOpsRing j)
      (instDiffRing i).toNonAssocSemiring (instDiffRing j).toNonAssocSemiring

end DModulesSheaf
end DModules
