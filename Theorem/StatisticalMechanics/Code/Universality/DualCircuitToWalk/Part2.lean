/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Def.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem dcw_dualBarrierGraph_le_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    dcw_dualBarrierGraph ω n ≤ openSubgraph 2 (dualConfig ω) := by
  rintro p q ⟨v, w, hvw, hpq⟩
  have hopen : (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) :=
    dcw_barrier_dualAdj ω n hvw
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq]; exact hopen
  · rw [hp, hq]; exact hopen.symm


end Universality
end StatMech
