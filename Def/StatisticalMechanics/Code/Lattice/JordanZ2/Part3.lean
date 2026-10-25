/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

noncomputable def faceBoundaryDegree (S : Set (Site 2)) (a b : ℤ) : ℕ :=
  bdInd S (faceCorner00 a b) (faceCorner10 a b)
    + bdInd S (faceCorner10 a b) (faceCorner11 a b)
    + bdInd S (faceCorner11 a b) (faceCorner01 a b)
    + bdInd S (faceCorner01 a b) (faceCorner00 a b)


end Lattice
end StatMech
