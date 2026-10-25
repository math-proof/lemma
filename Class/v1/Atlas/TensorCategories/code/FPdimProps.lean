/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Def.v1.Atlas.TensorCategories.code.FPdimProps
set_option maxHeartbeats 800000


namespace CategoryTheory

open CategoryTheory MonoidalCategory Limits

/-- Bundle of combinatorial data witnessing the finiteness of a multitensor
category `C`: indexed simples and projective covers, structure constants
`N_{ij}^l`, Jordan–Hölder multiplicities, the dual involution, and the
projective-cover multiplicity identities used to formulate the
Frobenius–Perron results of EGNO §1.47. -/
class FiniteMultitensorDecompData (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] where
  I : Type*
  [instFintype : Fintype I]
  [instDecEq : DecidableEq I]
  simpleObj : I → C
  simpleObj_simple : ∀ i, Simple (simpleObj i)
  projCover : I → C
  projCover_projective : ∀ i, Projective (projCover i)
  dualIndex : I → I
  structConst : I → I → I → ℕ
  structConst_eq : ∀ i j l,
    structConst i j l = Module.finrank k (simpleObj i ⊗ simpleObj j ⟶ simpleObj l)
  jhMult : C → I → ℕ
  hom_projCover_eq_mult : ∀ (i : I) (Y : C),
    Module.finrank k (projCover i ⟶ Y) = jhMult Y i
  projDecompMult : C → I → ℕ
  projDecompMult_eq_hom : ∀ (Q : C) [Projective Q] (k' : I),
    projDecompMult Q k' = Module.finrank k (Q ⟶ simpleObj k')
  jhMult_tensor_dual_eq : ∀ (k' i : I) (Z : C),
    jhMult (simpleObj k' ⊗ Zᘁ) i =
      ∑ l : I, structConst k' (dualIndex i) l * jhMult Z l
  jhMult_leftdual_tensor_eq : ∀ (k' i : I) (Z : C),
    jhMult ((ᘁZ) ⊗ simpleObj k') i =
      ∑ l : I, structConst l k' i * jhMult Z l

end CategoryTheory
