/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwGraphFormalRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) : MvPowerSeries (Sym2 V) ℂ :=
  PowerSeries.subst (kwGraphFormalLog G phase) (PowerSeries.exp ℂ)

end StatMech.FrontierA
