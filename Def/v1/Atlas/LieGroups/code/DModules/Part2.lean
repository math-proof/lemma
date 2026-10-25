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
import Structure.v1.Atlas.LieGroups.code.DModules
universe u v w


namespace DModules

open scoped TensorProduct

section DModulesSheaf

variable {k : Type u} [CommRing k]

noncomputable def SheafOfDiffOps.baseChangeType
    (D : SheafOfDiffOps.{u, v, w} k) {i j : D.I} (h : D.incl i j)
    (Mi : Type w) (inst_acg : AddCommGroup Mi)
    (inst_mod : @Module (D.diffOpsRing i) Mi (D.instDiffRing i).toSemiring
      inst_acg.toAddCommMonoid) : Type w :=
  @TensorProduct (D.coordRing i) (D.instCommRing i).toCommSemiring (D.coordRing j) Mi
    (D.instCommRing j).toAddCommMonoid inst_acg.toAddCommMonoid
    (@Module.compHom (D.coordRing j) (D.coordRing i) (D.coordRing j)
      (D.instCommRing j).toSemiring (D.instCommRing j).toAddCommMonoid
      (@Semiring.toModule _ (D.instCommRing j).toSemiring)
      (D.instCommRing i).toSemiring (D.coordRestrict h))
    (@Module.compHom (D.diffOpsRing i) (D.coordRing i) Mi
      (D.instDiffRing i).toSemiring inst_acg.toAddCommMonoid inst_mod
      (D.instCommRing i).toSemiring
      (@algebraMap (D.coordRing i) (D.diffOpsRing i) (D.instCommRing i).toCommSemiring
        (D.instDiffRing i).toSemiring (D.instDiffAlgebra i)))

@[reducible] noncomputable def SheafOfDiffOps.baseChangeAddCommGroup
    (D : SheafOfDiffOps.{u, v, w} k) {i j : D.I} (h : D.incl i j)
    (Mi : Type w) (inst_acg : AddCommGroup Mi)
    (inst_mod : @Module (D.diffOpsRing i) Mi (D.instDiffRing i).toSemiring
      inst_acg.toAddCommMonoid) : AddCommGroup (D.baseChangeType h Mi inst_acg inst_mod) :=
  @TensorProduct.addCommGroup (D.coordRing i) (D.instCommRing i).toCommSemiring
    (D.coordRing j) Mi ((D.instCommRing j).toRing.toAddCommGroup) inst_acg.toAddCommMonoid
    (@Module.compHom (D.coordRing j) (D.coordRing i) (D.coordRing j)
      (D.instCommRing j).toSemiring (D.instCommRing j).toAddCommMonoid
      (@Semiring.toModule _ (D.instCommRing j).toSemiring)
      (D.instCommRing i).toSemiring (D.coordRestrict h))
    (@Module.compHom (D.diffOpsRing i) (D.coordRing i) Mi
      (D.instDiffRing i).toSemiring inst_acg.toAddCommMonoid inst_mod
      (D.instCommRing i).toSemiring
      (@algebraMap (D.coordRing i) (D.diffOpsRing i) (D.instCommRing i).toCommSemiring
        (D.instDiffRing i).toSemiring (D.instDiffAlgebra i)))

end DModulesSheaf
end DModules
