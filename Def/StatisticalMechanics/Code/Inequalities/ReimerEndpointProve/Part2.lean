/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve
open Finset MeasureTheory
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {α : Type*}


def leftCfg (ω : ConfigSpace (α ⊕ α)) : ConfigSpace α := fun a => ω (Sum.inl a)


def rightCfg (ω : ConfigSpace (α ⊕ α)) : ConfigSpace α := fun a => ω (Sum.inr a)


def leftEvent (A : Set (ConfigSpace α)) : Set (ConfigSpace (α ⊕ α)) := {ω | leftCfg ω ∈ A}


def rightEvent (B : Set (ConfigSpace α)) : Set (ConfigSpace (α ⊕ α)) := {ω | rightCfg ω ∈ B}

end StatMech
