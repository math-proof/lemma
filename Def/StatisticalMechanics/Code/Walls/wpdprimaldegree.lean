module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
public import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
public import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
public import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
public import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
public import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
public import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
public import Theorem.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part5
public import Theorem.StatisticalMechanics.Code.Walls.wosorientedsign.Part2
public import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
public import Theorem.StatisticalMechanics.Code.Walls.woborientbridge.Part4
public import Theorem.StatisticalMechanics.Code.Walls.wpdprimaldegree
open Finset Set SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.Walls


def wpd_UpEntersInterior (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  wel_OrientationConsistent z Vc


end Lattice
end StatMech
