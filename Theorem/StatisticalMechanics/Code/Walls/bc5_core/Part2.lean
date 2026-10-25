/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc3_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc4_core
import Theorem.StatisticalMechanics.Code.Walls.bc5_barrierblocks.Part2
import Def.StatisticalMechanics.Code.Walls.bc5_core
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc5_boxForcedCorridorRouting_of_box {n : ℕ} (h : bc5_BoxCorridorRouting d n) :
    bc2_BoxForcedCorridorRouting d n := by
  intro ω hω
  obtain ⟨j₁, j₂, j₃, L₁, L₂, L₃, ⟨hj12, hj13, hj23⟩, ⟨hi1, hi2, hi3⟩, hdisj⟩ := h ω hω
  exact bc5_forcedCorridorRouting_of_disjoint ω hj12 hj13 hj23 hi1 hi2 hi3 hdisj


theorem bc5_burtonKeane_uniqueness_of_disjoint
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hroute : ∀ n : ℕ, bc5_BoxCorridorRouting d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc2_burtonKeane_uniqueness_of_box μ herg hfe bdry hbound hvol hdens
    (fun n => bc5_boxForcedCorridorRouting_of_box (hroute n))


theorem bc5_crossDisjoint_bot {a c : Fin d} (hac : a ≠ c) (R L : ℕ) :
    bc3_CrossDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) a c R L :=
  bc3_crossDisjoint_bot hac R L


theorem bc5_corridorClustersDisjoint_bot {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) (L₁ L₂ L₃ : ℕ) :
    bc3_CorridorClustersDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃ :=
  bc3_corridorClustersDisjoint_bot hj12 hj13 hj23 L₁ L₂ L₃


theorem bc5_pairwiseSeparated_bot {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) (L₁ L₂ L₃ : ℕ) :
    bc2_PairwiseSeparated (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃ :=
  bc5_pairwiseSeparated_of_corridorClustersDisjoint _ j₁ j₂ j₃ L₁ L₂ L₃
    (bc5_corridorClustersDisjoint_bot hj12 hj13 hj23 L₁ L₂ L₃)


theorem bc5_core (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    (bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ →
        bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃) ∧
      (j₁ ≠ j₂ → j₁ ≠ j₃ → j₂ ≠ j₃ →
        bc2_PairwiseSeparated (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃) :=
  ⟨fun h => bc5_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h,
    fun hj12 hj13 hj23 => bc5_pairwiseSeparated_bot hj12 hj13 hj23 L₁ L₂ L₃⟩

end Walls
end StatMech
