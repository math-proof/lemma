/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterContour.Part2
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


def InteriorAssignment : Type :=
  (u : Site 2) → (hypercubicLattice 2).Walk u u → Finset (Site 2)


def OuterContourMap (n : ℕ) : Prop :=
  ∃ interiorOf : InteriorAssignment,
    
    
    
    
    (∀ (ℓ : ℕ) (u : Site 2) (γ : (hypercubicLattice 2).Walk u u),
        u ∈ anchorFinset ℓ → γ.length = ℓ → γ.IsCycle →
          (↑(interiorOf u γ) : Set (Site 2)) ⊆ box 2 n ∧
          contourLen (↑(interiorOf u γ)) (bondFinsetTouch 2 n) = ℓ) ∧
    
    (∀ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false →
      ∃ (ℓ : ℕ) (u : Site 2) (γ : (hypercubicLattice 2).Walk u u),
        u ∈ anchorFinset ℓ ∧ γ.length = ℓ ∧ γ.IsCycle ∧
        ContourEvent (↑(interiorOf u γ)) (bondFinsetTouch 2 n) (glue (plusField 2) τ))


noncomputable def poc_circuitFamily (M : ℕ) :
    Finset (Σ _ℓ : ℕ, Σ u : Site 2, (hypercubicLattice 2).Walk u u) :=
  (Finset.range M).sigma (fun ℓ => Percolation.cyclesAtLen ℓ)


noncomputable def poc_circuitSummand (n : ℕ) (β : ℝ) (interiorOf : InteriorAssignment)
    (σ : Σ _ℓ : ℕ, Σ u : Site 2, (hypercubicLattice 2).Walk u u) : ℝ :=
  probContour (↑(interiorOf σ.2.1 σ.2.2)) (plusField 2) n (bondFinsetTouch 2 n) β


end Ising
end StatMech
