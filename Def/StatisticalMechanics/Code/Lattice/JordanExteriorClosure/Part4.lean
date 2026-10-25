/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part3
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


open Classical in


noncomputable def jec_rayCount (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  w.edges.countP (fun e => decide (jec_rayEdge z e))

open Classical in


noncomputable def jec_wallCount (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  w.edges.countP (fun e => decide (jec_wallEdge z e))

end Lattice
end StatMech
