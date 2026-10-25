/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open Classical in


noncomputable def wnd_signedCross (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℤ :=
  (w.darts.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).sum

end Lattice
end StatMech
