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
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part4
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


def jec_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Set (Site 2) :=
  {z | ¬ Even (jec_rayCount z Vc)}

end Lattice
end StatMech
