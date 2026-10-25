/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

open StatMech.Percolation

variable {d : ℕ}


def gvUnit (d : ℕ) (i : Fin d) : Site d := fun j => if j = i then 1 else 0


noncomputable def gvBall (x : Site d) : Finset (Site d) :=
  insert x ((Finset.univ : Finset (Fin d)).biUnion
    (fun i => {x + gvUnit d i, x - gvUnit d i}))


noncomputable def gvCand (S : Finset (Site d)) : Finset (Site d) := S.biUnion gvBall


noncomputable def gvBondTouch (S : Finset (Site d)) : Finset (Sym2 (Site d)) :=
  (((gvCand S) ×ˢ (gvCand S)).filter
    (fun p => (hypercubicLattice d).Adj p.1 p.2 ∧ (p.1 ∈ S ∨ p.2 ∈ S))).image (fun p => s(p.1, p.2))


end Ising
end StatMech
