/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterBridgeCalculus
open Finset Filter
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


def replicaBridgeMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiExp2 G J hf (fun a b =>
    Real.exp (r * replicaBridgeInteraction sites a b))


def replicaBridgeMean
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiExp2 G J hf (fun a b =>
      replicaBridgeInteraction sites a b *
        Real.exp (r * replicaBridgeInteraction sites a b)) /
    replicaBridgeMoment G J hf sites r


def replicaBridgeVariance
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiExp2 G J hf (fun a b =>
      replicaBridgeInteraction sites a b ^ 2 *
        Real.exp (r * replicaBridgeInteraction sites a b)) /
      replicaBridgeMoment G J hf sites r -
    replicaBridgeMean G J hf sites r ^ 2


def replicaBridgeFreeEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  Real.log (replicaBridgeMoment G J hf sites r) -
    Real.log (replicaBridgeMoment G J hf sites (-r))

end
end StatMech.Ising
