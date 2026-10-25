/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalEndpoint
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle


namespace StatMech.Onsager

open Matrix BigOperators


noncomputable def ons_decMiddleDestFactor
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L) (mu : Fin 4) : ℂ :=
  match mu with
  | 0 => decWeight (ons_decChainEdge site 0)
  | 1 => 1
  | 2 => 1
  | 3 => decWeight (ons_decChainEdge site 2)


noncomputable def ons_decMiddleSourceFactor
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L) (mu : Fin 4) : ℂ :=
  match mu with
  | 0 => 1
  | 1 => decWeight (ons_decChainEdge site 2)
  | 2 => decWeight (ons_decChainEdge site 0)
  | 3 => 1


noncomputable def ons_decMiddleU
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega : ℂ) (site : ZMod L × ZMod L) :
    Matrix (ons_Dart L) (Fin 2) ℂ :=
  fun d side ↦
    if d.1 = site ∧ ons_decMiddleSide d.2 = side then
      ons_decMiddleDestFactor decWeight site d.2 *
        ons_turnW omega (ons_decMiddleDir side) d.2
    else 0


noncomputable def ons_decMiddleV
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega u v : ℂ) (site : ZMod L × ZMod L) :
    Matrix (Fin 2) (ons_Dart L) ℂ :=
  fun side d ↦
    if site = ons_dirStep L d.2 d.1 ∧
        ons_decMiddleSide d.2 = side then
      decWeight (ons_decChainEdge site 1) *
        ons_dirPhase u v d.2 *
        decWeight s(d, ons_dartRev L d) *
        ons_decMiddleSourceFactor decWeight site d.2 *
        ons_turnW omega d.2 (ons_decMiddleDir side)
    else 0

end StatMech.Onsager
