/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourLinksExits
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


@[simp] theorem exitDart_tail (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitDart (ω := ω) hfin).tail = axisSite (exitIndex (ω := ω) hfin) := rfl

@[simp] theorem exitDart_head (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitDart (ω := ω) hfin).head = axisSite (exitIndex (ω := ω) hfin + 1) := rfl


theorem exitDart_isBoundaryDart (hfin : (cluster 2 ω (origin 2)).Finite) :
    IsBoundaryDart (cluster 2 ω (origin 2)) (exitDart (ω := ω) hfin) :=
  ⟨axisSite_exit_mem (ω := ω) hfin, axisSite_exit_succ_not_mem (ω := ω) hfin⟩


theorem exitDart_dir (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitDart (ω := ω) hfin).dir = ![1, 0] := by
  rw [Dart.dir_def, exitDart_head, exitDart_tail]
  funext i; fin_cases i <;> simp [axisSite]


end Lattice
end StatMech
