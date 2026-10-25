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
import Theorem.v1.Atlas.LieGroups.code.HeckeKL.Part2


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

def RPoly (C : CoxeterGroupData) (x y : C.W) : Polynomial ℤ :=
  if hy : y = 1 then (if x = 1 then 1 else 0)
  else
    let s := C.descentRefl y
    let sy := s * y
    let sx := s * x
    if C.length sx < C.length x then
      RPoly C sx sy
    else
      (Polynomial.X - Polynomial.C 1) * RPoly C x sy + Polynomial.X * RPoly C sx sy
termination_by C.length y
decreasing_by all_goals exact C.descentRefl_length y hy

def polyEvalQInv (p : Polynomial ℤ) : HeckeCoeffRing :=
  p.eval₂ (Int.castRingHom (LaurentPolynomial ℤ)) (LaurentPolynomial.T (-2))

def D_on_basis (C : CoxeterGroupData) (w : C.W) : HeckeAlgebra C :=
  ∑ x : C.W, Finsupp.single x
    (LaurentPolynomial.T (-(2 * (C.length x : ℤ))) * polyEvalQInv (RPoly C x w))

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

def HeckeAlgebra.D (C : CoxeterGroupData) : HeckeAlgebra C → HeckeAlgebra C :=
  fun h => h.sum fun w aw => coeffInvolution aw • D_on_basis C w

end
