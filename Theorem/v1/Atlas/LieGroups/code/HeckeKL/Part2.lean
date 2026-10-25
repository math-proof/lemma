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
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part5


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

theorem coeffInvolution_eq_ringHom (a : HeckeCoeffRing) :
    coeffInvolution a = coeffInvolutionRingHom a := by
  simp [coeffInvolution, coeffInvolutionRingHom, AddMonoidAlgebra.mapDomainRingHom,
        AddMonoidAlgebra.mapDomain, negAddHom]

theorem coeffInvolution_zero : coeffInvolution 0 = 0 := by
  rw [coeffInvolution_eq_ringHom]; exact map_zero coeffInvolutionRingHom

theorem coeffInvolution_add (a b : HeckeCoeffRing) :
    coeffInvolution (a + b) = coeffInvolution a + coeffInvolution b := by
  unfold coeffInvolution
  exact Finsupp.mapDomain_add

end
