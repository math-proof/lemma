/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzFourPoint
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterStrongMarkedSite
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness StatMech.FrontierA

open StatMech.Sharpness.FieldGhostDict

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def lpGhostCoupling (J : Sym2 V -> Real) (hf : V -> Real) :
    Sym2 (Option V) -> Real :=
  Sym2.lift ⟨fun a b =>
    match a, b with
    | some x, some y => J s(x, y)
    | some x, none => hf x
    | none, some y => hf y
    | none, none => 0,
    by rintro (_ | x) (_ | y) <;> simp only [] <;> rw [Sym2.eq_swap]⟩

end
end StatMech.Ising
