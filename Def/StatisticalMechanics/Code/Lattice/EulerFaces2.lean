/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2
open SimpleGraph Set


set_option linter.unusedSectionVars false


namespace StatMech.Lattice

variable {V : Type*}


variable [Finite V] [DecidableEq V]


noncomputable def nullity (G : SimpleGraph V) : ℕ :=
  (G.edgeSet.ncard + Nat.card G.ConnectedComponent) - Nat.card V


noncomputable def faceCount (G : SimpleGraph V) : ℕ := nullity G + 1


end StatMech.Lattice
