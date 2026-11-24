module
public import Theorem.StatisticalMechanics.Code.Probability.HCTensorLib
public import Theorem.StatisticalMechanics.Code.Probability.PBiasedHCLib.Part3
public import Theorem.StatisticalMechanics.Code.Probability.SharpThresholdWire
open scoped BigOperators
open Finset
open Real Set
open StatMech StatMech.OSSS
set_option linter.style.longLine false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Probability

def stw_RemainingGoal (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p


end StatMech.Probability
