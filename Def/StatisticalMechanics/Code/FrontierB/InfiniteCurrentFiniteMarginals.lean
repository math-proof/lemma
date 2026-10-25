/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentFiniteMarginals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology.Part8
open Filter MeasureTheory Topology


namespace StatMech

namespace FrontierB

def currentCylinder {E : Type*} (S : Finset E) (A : Set (↑S → ℕ)) :
    Set (InfiniteCurrentConfig E) := restrictCurrent S ⁻¹' A


end FrontierB
end StatMech
