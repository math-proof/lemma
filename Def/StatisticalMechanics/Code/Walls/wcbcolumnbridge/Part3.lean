module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
public import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
public import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
public import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
public import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part2
open Finset Set SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable def wcb_keyedList (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : List (ℤ × ℤ) :=
  (w.darts.map (fun d => (wcb_dartColumn d, wnd_signStep z d.toProd.1 d.toProd.2))).filter
    (fun p => p.2 ≠ 0)


end Lattice
end StatMech
