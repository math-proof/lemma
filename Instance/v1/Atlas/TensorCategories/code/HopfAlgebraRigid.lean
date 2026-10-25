/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebraRigid.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.RepresentationTheory.FDRep
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra WithConv LinearMap
open scoped TensorProduct

universe u v


section Corollary_1_22_6

open CategoryTheory


/-- Corollary 1.22.6(i): if `H` is a bialgebra with an antipode `S`, then the abelian monoidal
category `Rep(H)` has right duals — namely the linear dual `V^*` with `H`-action via
`ρ_{V^*}(a) = ρ_V(S(a))^*`. -/
@[reducible]
noncomputable instance Corollary_1_22_6_right_rigid_group
    (k G : Type u) [Field k] [Group G] :
    RightRigidCategory (FDRep k G) :=
  inferInstance

/-- Instance of Corollary 1.22.6(ii) for a group algebra: `FDRep k G` is rigid (i.e. a
tensor category). -/
noncomputable instance Corollary_1_22_6_rigid_group
    (k G : Type u) [Field k] [Group G] :
    RigidCategory (FDRep k G) :=
  inferInstance

end Corollary_1_22_6
