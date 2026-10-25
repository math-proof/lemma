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
import Instance.v1.Atlas.LieGroups.code.HeckeKL.Part2


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

def HeckeAlgebra.T (C : CoxeterGroupData) (w : C.W) : HeckeAlgebra C :=
  Finsupp.single w 1

def simpleReflMulBasis (C : CoxeterGroupData) (s w : C.W) : HeckeAlgebra C :=
  if C.length (s * w) = C.length w + 1 then
    Finsupp.single (s * w) 1
  else
    Finsupp.single w (hecke_q - 1) + Finsupp.single (s * w) hecke_q

def simpleActOnLinComb (C : CoxeterGroupData) (s : C.W) (f : HeckeAlgebra C) : HeckeAlgebra C :=
  f.sum fun w c => c • simpleReflMulBasis C s w

def heckeMulBasis (C : CoxeterGroupData) (w₁ w₂ : C.W) : HeckeAlgebra C :=
  if hw₁ : w₁ = 1 then Finsupp.single w₂ 1
  else
    let s := C.descentRefl w₁
    let w₁' := s * w₁
    simpleActOnLinComb C s (heckeMulBasis C w₁' w₂)
termination_by C.length w₁
decreasing_by exact C.descentRefl_length w₁ hw₁

def heckeMul (C : CoxeterGroupData) (f g : HeckeAlgebra C) : HeckeAlgebra C :=
  f.sum fun w₁ a₁ => g.sum fun w₂ a₂ =>
    (a₁ * a₂) • heckeMulBasis C w₁ w₂

end
