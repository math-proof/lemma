/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FrobeniusPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Def.v1.Atlas.TensorCategories.code.PerronFrobeniusProof.Part2
public import Theorem.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
public import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part4
@[expose] public section

set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- General `HasPerronFrobeniusProperty` instance combining the existence
result `perronFrobeniusExistence` with the uniqueness
`PerronFrobeniusGeneral.pfUnique_general`. -/
noncomputable instance instHasPerronFrobeniusPropertyGeneral
    (ι : Type*) [DecidableEq ι] [Fintype ι] [Nonempty ι] :
    FusionRing.HasPerronFrobeniusProperty ι where
  pfEigenvec := fun M hM => perronFrobeniusExistence M hM
  pfUnique := fun M hM r₁ r₂ v w hv hev hw hew =>
    PerronFrobeniusGeneral.pfUnique_general M hM r₁ r₂ v w hv hev hw hew

end FusionRing
