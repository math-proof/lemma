/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerSeparation.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    SimpleGraph (Site 2) where
  Adj x y := (hypercubicLattice 2).Adj x y ∧ x ∉ Vc.support ∧ y ∉ Vc.support
  symm := by
    constructor
    intro x y ⟨hadj, hx, hy⟩
    exact ⟨hadj.symm, hy, hx⟩
  loopless := ⟨fun x h => (hypercubicLattice 2).irrefl h.1⟩

end Lattice
end StatMech
