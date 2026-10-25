/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
import Theorem.StatisticalMechanics.Code.Onsager.KWLoopWeight


namespace StatMech.Onsager

open Matrix BigOperators

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.GeneralUmlaufsatz


def ons_reduceSite (L : ℕ) (p : ℤ × ℤ) : ZMod L × ZMod L :=
  ((p.1 : ZMod L), (p.2 : ZMod L))


def ons_liftDir {L n : ℕ} [NeZero n] (v : Fin n → ons_Dart L) : Fin n → Fin 4 :=
  fun k => (v (-k)).2


def ons_liftSite {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) : Fin n → ZMod L × ZMod L :=
  fun k => (v (-k)).1

end StatMech.Onsager
