/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HeckeKL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.LieGroups.code.CompositionSeries
import Lemma.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part7


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

structure CoxeterWeylCompatibility
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (C : CoxeterGroupData)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) where
  ι : C.W ≃* wg.W

end
