/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P5Equivalences.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Def.StatisticalMechanics.Code.RSW.P5Equivalences
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


@[simp] theorem mem_annulusEvent {n : ℕ} {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ annulusEvent n ↔ AnnulusCircuit ω (fun _ => 0) n := Iff.rfl


end Box
end RSW
end StatMech
