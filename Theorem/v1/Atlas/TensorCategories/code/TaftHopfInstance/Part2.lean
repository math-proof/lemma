/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.TaftConcrete.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.TaftConcrete
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
import Instance.v1.Atlas.TensorCategories.code.TaftHopfInstance
open Coalgebra HopfAlgebra
open scoped TensorProduct


namespace TaftAlgebraType

variable (k : Type*) [Field k] (n : ℕ) [NeZero n] (q : k) [Fact (q ^ n = 1)]


local notation "A" => TaftAlgebraType n q k

variable [TaftHopfData k n q]

noncomputable section

/-- The instance-level comultiplication on `A` agrees with `taftComulLM`. -/
@[simp] lemma taft_comul_is [TaftHopfData k n q] :
    (CoalgebraStruct.comul : A →ₗ[k] _) = taftComulLM k n q := rfl

/-- The instance-level counit on `A` agrees with `taftCounitLM`. -/
@[simp] lemma taft_counit_is [TaftHopfData k n q] :
    (CoalgebraStruct.counit : A →ₗ[k] k) = taftCounitLM k n q := rfl

end
end TaftAlgebraType
