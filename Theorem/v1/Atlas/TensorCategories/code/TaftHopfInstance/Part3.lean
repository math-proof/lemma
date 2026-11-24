module
public import Theorem.v1.Atlas.TensorCategories.code.TaftConcrete.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.TaftConcrete
public import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
public import Instance.v1.Atlas.TensorCategories.code.TaftHopfInstance.Part2
open Coalgebra HopfAlgebra
open scoped TensorProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace TaftAlgebraType

variable (k : Type*) [Field k] (n : ℕ) [NeZero n] (q : k) [Fact (q ^ n = 1)]


local notation "A" => TaftAlgebraType n q k

variable [TaftHopfData k n q]

noncomputable section

/-- The instance-level antipode on `A` agrees with `taftAntipodeLM`. -/
@[simp] lemma taft_antipode_is [TaftHopfData k n q] :
    (HopfAlgebraStruct.antipode (R := k) : A →ₗ[k] _) =
      taftAntipodeLM k n q := rfl

end
end TaftAlgebraType
