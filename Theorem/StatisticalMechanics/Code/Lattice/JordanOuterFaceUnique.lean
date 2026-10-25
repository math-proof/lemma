/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem outerBoxRadius_spec (P : PlanarZ2Subgraph) :
    ∀ v : P.V, P.emb v ∈ box 2 (outerBoxRadius P) :=
  (image_subset_box P).choose_spec


end Lattice
end StatMech
