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
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness StatMech.FrontierA

open StatMech.Sharpness.FieldGhostDict

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def lpFieldUrsell4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (i j k l : V) : Real :=
  expJ G.edgeFinset J hf
      (fun s => (spin s i * spin s j) * (spin s k * spin s l)) -
    expJ G.edgeFinset J hf (fun s => spin s i * spin s j) *
      expJ G.edgeFinset J hf (fun s => spin s k * spin s l) -
    expJ G.edgeFinset J hf (fun s => spin s i * spin s k) *
      expJ G.edgeFinset J hf (fun s => spin s j * spin s l) -
    expJ G.edgeFinset J hf (fun s => spin s i * spin s l) *
      expJ G.edgeFinset J hf (fun s => spin s j * spin s k)

end
end StatMech.Ising
