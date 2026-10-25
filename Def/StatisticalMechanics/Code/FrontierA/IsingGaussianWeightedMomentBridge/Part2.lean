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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedMomentBridge
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteIsingWeightedRawMoment
    (beta : Real) (a : V -> Real) (order : Nat) : Real :=
  (∑ s : ConfigSpace V,
      zeroFieldInteractionWeight G beta s *
        finiteIsingWeightedSpinReal a s ^ order) /
    ∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s


def finiteIsingWeightedMomentGeneratingFunction
    (beta : Real) (a : V -> Real) (z : Complex) : Complex :=
  finiteIsingWeightedFieldPartition G beta a z /
    finiteIsingWeightedFieldPartition G beta a 0


end
end StatMech.FrontierA
