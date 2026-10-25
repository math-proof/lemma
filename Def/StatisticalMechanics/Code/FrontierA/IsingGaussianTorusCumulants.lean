/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusScalingHandoff
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part19
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardCumulants.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusCumulants
open Filter MeasureTheory Topology
open scoped BigOperators


namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising StatMech.FrontierB

noncomputable section

variable {d k : Nat}


def isingTorusScaledSmearedField
    (c : Real) (a : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) : Real :=
  c * isingTorusSmearedSpin a sigma


def isingTorusScaledSmearedCumulant
    (beta c t : Real) (a : IsingDyadicTorus d k → Real)
    (order : Nat) : Real :=
  scalarCumulantsOfMoments
    (fun m => (t * c) ^ m *
      finiteIsingWeightedRawMoment
        (isingTorusGraph d k) beta a m) order


end
end StatMech.FrontierA
