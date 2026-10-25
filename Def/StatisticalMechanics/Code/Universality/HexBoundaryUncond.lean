/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContourDecomp.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part4


namespace StatMech.Universality

open Complex

open scoped BigOperators


noncomputable def hexUncondMid (a : ℂ) (h0 : ℤ) : Fin 3 → ℂ
  | 0 => hexConcreteV a h0 + hexConcreteDu a h0
  | 1 => hexConcreteV a h0 + hexOmega * hexConcreteDu a h0
  | 2 => hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0


noncomputable def hexUncondObs (a : ℂ) (h0 : ℤ) (z : ℂ) : ℂ :=
  parafObservable (hexVBCRegion a h0).inRegion a h0 z (5/8) hexChi


noncomputable def hexUncondDomain (a : ℂ) (h0 : ℤ) : HexDomain (Fin 1) where
  interiorVertices := {0}
  pos := fun _ => hexConcreteV a h0
  mid := fun _ => hexUncondMid a h0
  obs := hexUncondObs a h0
  relation := by
    intro v _
    
    rw [Fin.sum_univ_three]
    change (hexUncondMid a h0 0 - hexConcreteV a h0) * hexUncondObs a h0 (hexUncondMid a h0 0)
        + (hexUncondMid a h0 1 - hexConcreteV a h0) * hexUncondObs a h0 (hexUncondMid a h0 1)
        + (hexUncondMid a h0 2 - hexConcreteV a h0) * hexUncondObs a h0 (hexUncondMid a h0 2) = 0
    unfold hexUncondMid hexUncondObs
    exact hexVBC_vertex_relation_unconditional a h0


end StatMech.Universality
