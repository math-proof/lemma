/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeGraham
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeActual
open Finset SimpleGraph


namespace StatMech.Ising

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

variable {V : Type*}


variable [Fintype V] [DecidableEq V]


def threeBridgeOneCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) : Real :=
  (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s z)) ^ 2


def threeBridgeTwoCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) : Real :=
  (expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s x * spin s z)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s y * spin s z)) ^ 2


def threeBridgeThreeCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) : Real :=
  (expJ G.edgeFinset J hf
    (fun s => spin s x * (spin s y * spin s z))) ^ 2


def threeBridgeTiltMean (t a b c : Real) : Real :=
  3 * t + (1 - t ^ 2) * (a + 2 * b * t + 3 * c * t ^ 2) /
    (1 + a * t + b * t ^ 2 + c * t ^ 3)


end
end StatMech.Ising
