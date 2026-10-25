/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman
open Filter Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

section FiniteTotalSpin

variable {V : Type*} [Fintype V] [DecidableEq V]


def finiteParityTotalSpinSecondMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) : Real :=
  ∑ i : V, ∑ j : V,
    expectationJ G beta J (grahamPairSupport i j)


def finiteParityTotalSpinFourthMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) : Real :=
  ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
    expectationJ G beta J (grahamFourSupport i j k l)

end FiniteTotalSpin
end
end StatMech.FrontierA
