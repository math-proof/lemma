/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_contoureulerone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
open SimpleGraph


namespace StatMech.Walls

open StatMech.Lattice


noncomputable def contourEulerChar (p : ℕ) : ℕ := by
  classical
  exact if 3 ≤ p then cyclomaticNumber (cycleGraph p) else 0


end StatMech.Walls
