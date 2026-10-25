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
import Theorem.v1.Atlas.LieGroups.code.HeckeKL.Part3


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

noncomputable def HeckeAlgebra.D_addHom (C : CoxeterGroupData) :
    HeckeAlgebra C →+ HeckeAlgebra C where
  toFun := HeckeAlgebra.D C
  map_zero' := HeckeAlgebra.D_zero C
  map_add' := HeckeAlgebra.D_add C

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

noncomputable def D_coeff (C : CoxeterGroupData) (x w : C.W) : HeckeCoeffRing :=
  LaurentPolynomial.T (-(2 * (C.length x : ℤ))) * polyEvalQInv (RPoly C x w)

def mkBoundedPoly (bound : ℕ) (coeffs : ℕ → ℤ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (bound + 1), Polynomial.C (coeffs i) * Polynomial.X ^ i

def middleCoeffs (C : CoxeterGroupData) (y _w : C.W)
    (rec_val : C.W → Polynomial ℤ) : Polynomial ℤ :=
  ∑ z : C.W, Polynomial.C ((-1 : ℤ) ^ (C.length y + C.length z)) * RPoly C y z * rec_val z

def self_dual_coeffs (C : CoxeterGroupData) (y w : C.W)
    (_bound : ℕ) (rec_val : C.W → Polynomial ℤ) : ℕ → ℤ :=
  fun (j : ℕ) => (middleCoeffs C y w rec_val).coeff j

def KazhdanLusztigPoly (C : CoxeterGroupData) (y w : C.W) : Polynomial ℤ :=
  if ¬ C.bruhatLE y w then 0
  else if y = w then 1
  else
    let bound := (C.length w - C.length y - 1) / 2
    let rec_val : C.W → Polynomial ℤ := fun z =>
      if _h : C.bruhatLE y z ∧ z ≠ y ∧ C.bruhatLE z w then
        KazhdanLusztigPoly C z w
      else 0
    mkBoundedPoly bound (self_dual_coeffs C y w bound rec_val)
termination_by C.length w - C.length y
decreasing_by
  have hyz : C.bruhatLE y z := _h.1
  have hzy : z ≠ y := _h.2.1
  have hzw : C.bruhatLE z w := _h.2.2
  have : C.length y < C.length z := C.bruhat_length_strict y z hyz (Ne.symm hzy)
  have : C.length z ≤ C.length w := C.bruhat_length_le z w hzw
  omega

end
