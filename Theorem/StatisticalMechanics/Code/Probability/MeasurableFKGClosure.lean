/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Profinite
open Filter MeasureTheory Set Topology


namespace StatMech

variable {E : Type*} [DecidableEq E] [Countable E]

theorem isClopen_of_dependsOn_finset
    (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : DependsOn A (F : Set E)) : IsClopen A := by
  rw [ih_eq_cylinder_of_dependsOn F hA]
  exact isClopen_cylinderEvent F _


end StatMech
