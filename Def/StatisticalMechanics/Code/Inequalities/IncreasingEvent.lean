/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace


namespace StatMech

open ConfigSpace

variable {E : Type*}


def IsIncreasing (A : Set (ConfigSpace E)) : Prop := IsUpperSet A


def IsDecreasing (A : Set (ConfigSpace E)) : Prop := IsLowerSet A


def IsIncreasingFun (f : ConfigSpace E → ℝ) : Prop := Monotone f


def IsDecreasingFun (f : ConfigSpace E → ℝ) : Prop := Antitone f


end StatMech
