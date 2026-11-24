module
public import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
public import Theorem.StatisticalMechanics.Code.Inequalities.Harris
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
public import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part2
open MeasureTheory Set Filter
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

variable {E : Type*} [Countable E] [DecidableEq E]

def ih_section (A : Set (ConfigSpace E)) (F : Finset E) : Set (ConfigSpace F) :=
  {eta | ih_fill F eta ∈ A}

end StatMech
