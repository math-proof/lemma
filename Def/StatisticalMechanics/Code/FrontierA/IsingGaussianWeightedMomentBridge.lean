/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedHadamardPrereq
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedFourth.Part4
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteIsingWeightedSpin (a : V -> Real) (s : ConfigSpace V) : Complex :=
  ∑ v : V, (a v : Complex) * spin s v


def finiteIsingWeightedSpinReal (a : V -> Real) (s : ConfigSpace V) : Real :=
  ∑ v : V, a v * spin s v

end
end StatMech.FrontierA
