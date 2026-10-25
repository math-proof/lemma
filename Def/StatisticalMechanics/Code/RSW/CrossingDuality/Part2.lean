/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.RSW.CrossingDuality.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace RSW

namespace CrossingDuality

def rcd_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Set (Site 2) :=
  {v | v ∈ rect a b c d ∧ ∃ (x : Site 2) (hx : x ∈ leftSide a b c d) (hv : v ∈ rect a b c d),
      ConnectedWithin 2 ω (rect a b c d) ⟨x, leftSide_subset hx⟩ ⟨v, hv⟩}

end CrossingDuality
end RSW
end StatMech
