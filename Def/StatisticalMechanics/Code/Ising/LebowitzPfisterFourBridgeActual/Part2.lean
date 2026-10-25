/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeObstruction.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeActual
open Finset SimpleGraph


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*}


variable [Fintype V] [DecidableEq V]

def fourBridgeOneCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) : Real :=
  (expJ G.edgeFinset J hf (fun s => spin s w)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s z)) ^ 2

def fourBridgeTwoCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) : Real :=
  (expJ G.edgeFinset J hf (fun s => spin s w * spin s x)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s w * spin s y)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s w * spin s z)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s x * spin s z)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s y * spin s z)) ^ 2

def fourBridgeThreeCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) : Real :=
  (expJ G.edgeFinset J hf
      (fun s => spin s w * (spin s x * spin s y))) ^ 2 +
    (expJ G.edgeFinset J hf
      (fun s => spin s w * (spin s x * spin s z))) ^ 2 +
    (expJ G.edgeFinset J hf
      (fun s => spin s w * (spin s y * spin s z))) ^ 2 +
    (expJ G.edgeFinset J hf
      (fun s => spin s x * (spin s y * spin s z))) ^ 2

def fourBridgeFourCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) : Real :=
  (expJ G.edgeFinset J hf
    (fun s => spin s w * (spin s x * (spin s y * spin s z)))) ^ 2


end
end StatMech.Ising
