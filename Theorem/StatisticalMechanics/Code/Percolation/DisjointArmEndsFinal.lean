/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem daepf_shared_arm_reconnects (ω : ConfigSpace (Sym2 (Site d))) {x a b v : Site d}
    (hva : Connected d (removeSite x ω) a v) (hvb : Connected d (removeSite x ω) b v) :
    Connected d (removeSite x ω) a b :=
  hva.trans hvb.symm


theorem daepf_no_common_arm_vertex (ω : ConfigSpace (Sym2 (Site d))) {x a b : Site d}
    (hdis : ¬ Connected d (removeSite x ω) a b) :
    ∀ v, ¬ (Connected d (removeSite x ω) a v ∧ Connected d (removeSite x ω) b v) :=
  fun _v ⟨hva, hvb⟩ => hdis (daepf_shared_arm_reconnects ω hva hvb)


theorem daepf_arm_class_unique (ω : ConfigSpace (Sym2 (Site d))) {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₂ v) ∧
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₃ v) ∧
    ¬ (Connected d (removeSite x ω) a₂ v ∧ Connected d (removeSite x ω) a₃ v) :=
  ⟨daepf_no_common_arm_vertex ω hd12 v, daepf_no_common_arm_vertex ω hd13 v,
   daepf_no_common_arm_vertex ω hd23 v⟩


theorem daepf_in_some_or_no_arm (ω : ConfigSpace (Sym2 (Site d))) {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    (Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v ∧
        ¬ Connected d (removeSite x ω) a₃ v) ∨
    (Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₁ v ∧
        ¬ Connected d (removeSite x ω) a₃ v) ∨
    (Connected d (removeSite x ω) a₃ v ∧ ¬ Connected d (removeSite x ω) a₁ v ∧
        ¬ Connected d (removeSite x ω) a₂ v) ∨
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v ∧
        ¬ Connected d (removeSite x ω) a₃ v) := by
  classical
  by_cases h1 : Connected d (removeSite x ω) a₁ v
  · exact Or.inl ⟨h1, fun h2 => hd12 (h1.trans h2.symm), fun h3 => hd13 (h1.trans h3.symm)⟩
  · by_cases h2 : Connected d (removeSite x ω) a₂ v
    · exact Or.inr (Or.inl ⟨h2, h1, fun h3 => hd23 (h2.trans h3.symm)⟩)
    · by_cases h3 : Connected d (removeSite x ω) a₃ v
      · exact Or.inr (Or.inr (Or.inl ⟨h3, h1, h2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))


end Percolation
end StatMech
