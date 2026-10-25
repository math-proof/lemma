/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly.Part4


namespace StatMech.FrontierA

open scoped NNReal

open Set


noncomputable def KWStairParameterData.vertex
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) :
      Fin (n * (2 * S)) → ℂ :=
  fun j ↦ data.localVertex (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm j).2

def kwStairEvenIndex
    {n S : ℕ} [NeZero n] [NeZero S]
    (i : Fin n) (k : Fin S) : Fin (n * (2 * S)) :=
  finProdFinEquiv (i, kwStairEvenLocal k)

def kwStairOddIndex
    {n S : ℕ} [NeZero n] [NeZero S]
    (i : Fin n) (k : Fin S) : Fin (n * (2 * S)) :=
  finProdFinEquiv (i, kwStairOddLocal k)

end StatMech.FrontierA
