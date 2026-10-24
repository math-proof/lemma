/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_22_6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.RepresentationTheory.FDRep

set_option maxHeartbeats 400000

open CategoryTheory Coalgebra HopfAlgebra LinearMap
open scoped TensorProduct

universe u v


section DualActionAlgebraic

variable {k : Type u} [CommSemiring k] {H : Type v} [Semiring H] [HopfAlgebra k H]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module H V] [SMulCommClass k H V]

/-- The `k`-linear map `v ↦ h • v` on a Hopf-algebra module `V`. -/
noncomputable def corollary_1_22_6_smul_map (h : H) : V →ₗ[k] V where
  toFun v := h • v
  map_add' := smul_add h
  map_smul' r v := by
    dsimp
    haveI : SMulCommClass H k V := SMulCommClass.symm k H V
    rw [smul_comm]

/-- The dual right action of `H` on `V*`: `a · f = f ∘ (S(a) • -)`, used to give the linear
dual the structure of a right `H`-module via the antipode. -/
noncomputable def corollary_1_22_6_right_dual_action (a : H) (f : Module.Dual k V) :
    Module.Dual k V :=
  f.comp (corollary_1_22_6_smul_map (k := k) (antipode k a))

/-- Corollary 1.22.6 (EGNO, part (i)): the category `Rep(H)` of `H`-modules over a Hopf
algebra `H` admits right duals: for any object `X`, the right dual `X*` is the usual dual
space with action `ρ_{X*}(a) = ρ_X(S(a))*`. -/
@[reducible]
noncomputable instance corollary_1_22_6_right_rigid_group
    (k G : Type u) [Field k] [Group G] :
    RightRigidCategory (FDRep k G) :=
  inferInstance

/-- Instance specialization of Corollary 1.22.6 (ii) to the group case: `FDRep(k, G)` is
rigid. -/
noncomputable instance corollary_1_22_6_rigid_group
    (k G : Type u) [Field k] [Group G] :
    RigidCategory (FDRep k G) :=
  inferInstance

end CategoricalStatements
