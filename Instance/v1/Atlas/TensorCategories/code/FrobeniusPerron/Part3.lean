/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FrobeniusPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Def.v1.Atlas.TensorCategories.code.PerronFrobeniusProof.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part4
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
