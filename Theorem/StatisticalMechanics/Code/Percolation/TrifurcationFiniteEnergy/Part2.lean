/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Def.StatisticalMechanics.Code.Percolation.TrifurcationFiniteEnergy
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tfe_threeClustersReachOrigin_of_top (ω : ConfigSpace (Sym2 (Site d)))
    (htop : numInfiniteClusters d ω = ⊤)
    (hres : ∀ m : ℕ, tfe_BoxAttachResidue d m) :
    ∃ (n : ℕ) (W : Finset (Sym2 (Site d))),
      ω ∈ threeMeetBox d n ∧ mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
  obtain ⟨n, hω⟩ := tfe_threeMeetBox_of_top ω htop
  obtain ⟨x₁, x₂, x₃, ⟨hb1, hb2, hb3⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ :=
    tfe_three_distinct_infinite_of_box hω
  have hattach : tex_AttachData ω x₁ x₂ x₃ :=
    hres n ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hd12 hd13 hd23
  obtain ⟨W, hreach⟩ :=
    tfe_threeClustersReachOrigin_of_attach ω x₁ x₂ x₃ ⟨hd12, hd13, hd23⟩ hattach
  exact ⟨n, W, hω, hreach⟩


theorem tfe_routing_of_boxResidue {n : ℕ}
    (h : tfe_BoxAttachResidue d n) : hrHD_DisjointRouting d n :=
  tex_disjointRouting_of_box h


end Percolation
end StatMech
