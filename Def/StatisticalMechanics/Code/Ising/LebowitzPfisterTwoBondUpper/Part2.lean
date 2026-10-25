/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBondUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBondUpper.Part2
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBondUpper
open Set
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness


variable {V : Type*} [Fintype V] [DecidableEq V]


def twoReplicaTwoBridgeMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (r : Real) : Real :=
  ghsiExp2 G J hf (fun a b => Real.exp (r *
    (spin a x * spin b x + spin a y * spin b y)))


def twoReplicaTwoBridgeFreeEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (K : Real) : Real :=
  Real.log (twoReplicaTwoBridgeMoment G J hf x y K) -
    Real.log (twoReplicaTwoBridgeMoment G J hf x y (-K))


end
end StatMech.Ising
