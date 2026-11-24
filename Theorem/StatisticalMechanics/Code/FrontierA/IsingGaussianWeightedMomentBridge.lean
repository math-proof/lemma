module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedHadamardPrereq
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedFourth.Part4
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedMomentBridge
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedMomentBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem ofReal_finiteIsingWeightedSpinReal
    (a : V -> Real) (s : ConfigSpace V) :
    (finiteIsingWeightedSpinReal a s : Complex) =
      finiteIsingWeightedSpin a s := by
  simp [finiteIsingWeightedSpinReal, finiteIsingWeightedSpin]


end
end StatMech.FrontierA
