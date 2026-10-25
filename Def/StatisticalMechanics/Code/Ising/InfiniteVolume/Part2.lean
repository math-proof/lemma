/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
import Instance.StatisticalMechanics.Code.Ising.InfiniteVolume.Part2
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def bondPairsTouch (d n : ℕ) : Finset (Site d × Site d) :=
  ((boxFinset d (n + 1)) ×ˢ (boxFinset d (n + 1))).filter
    (fun p => (hypercubicLattice d).Adj p.1 p.2 ∧ (p.1 ∈ box d n ∨ p.2 ∈ box d n))


noncomputable def bondPairsInternal (d n : ℕ) : Finset (Site d × Site d) :=
  ((boxFinset d n) ×ˢ (boxFinset d n)).filter
    (fun p => (hypercubicLattice d).Adj p.1 p.2)


noncomputable def bondFinsetTouch (d n : ℕ) : Finset (Sym2 (Site d)) :=
  (bondPairsTouch d n).image (fun p => s(p.1, p.2))


noncomputable def bondFinsetInternal (d n : ℕ) : Finset (Sym2 (Site d)) :=
  (bondPairsInternal d n).image (fun p => s(p.1, p.2))


noncomputable def glue (η : ConfigSpace (Site d)) {n : ℕ}
    (τ : {x // x ∈ box d n} → Bool) : ConfigSpace (Site d) :=
  fun x => if h : x ∈ box d n then τ ⟨x, h⟩ else η x

end Ising
end StatMech
