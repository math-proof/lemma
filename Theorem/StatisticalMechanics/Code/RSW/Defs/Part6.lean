/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.RSW.Defs.Part6
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


@[simp] theorem mem_annulusCircuitEvent {z : Site 2} {n : ℕ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ annulusCircuitEvent z n ↔ AnnulusCircuit ω z n := Iff.rfl


end Box
end RSW
end StatMech
