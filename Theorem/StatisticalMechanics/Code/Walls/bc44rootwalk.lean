/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc44rootwalk.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc41rootside.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc42rootward.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc43rootparent
import Def.StatisticalMechanics.Code.Walls.bc44rootwalk
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


set_option linter.unusedSimpArgs false in


theorem bc44_farWitnessRank_distinct {x₀ y₀ z₀ : Site d}
    (hxy : x₀ ≠ y₀) (hxz : x₀ ≠ z₀) (hyz : y₀ ≠ z₀) {a b : Site d}
    (ha : a = x₀ ∨ a = y₀ ∨ a = z₀) (hb : b = x₀ ∨ b = y₀ ∨ b = z₀) (hab : a ≠ b) :
    bc44_farWitnessRank y₀ z₀ a ≠ bc44_farWitnessRank y₀ z₀ b := by
  intro heq
  have hab' : (if a = y₀ then (2 : ℕ) else if a = z₀ then 1 else 0)
      = (if b = y₀ then (2 : ℕ) else if b = z₀ then 1 else 0) := by
    have := congrArg (fun p => (ofLex p).1) heq
    simpa [bc44_farWitnessRank] using this
  
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | (simp only [↓reduceIte, if_neg hxy, if_neg hxz, if_neg hyz, if_neg (Ne.symm hxy),
        if_neg (Ne.symm hxz), if_neg (Ne.symm hyz)] at hab'; omega)


theorem bc44_farWitness_rank_injective (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ z₀ : Site d} (hxy : x₀ ≠ y₀) (hxz : x₀ ≠ z₀) (hyz : y₀ ≠ z₀)
    (hexhaust : ∀ a, a ∈ box d n → IsTrifurcation d ω a → a = x₀ ∨ a = y₀ ∨ a = z₀) :
    ∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b →
      a ≠ b → Connected d ω a b →
      bc44_farWitnessRank y₀ z₀ a ≠ bc44_farWitnessRank y₀ z₀ b := by
  intro a habox htria b hbbox htrib hab _hconn
  exact bc44_farWitnessRank_distinct hxy hxz hyz
    (hexhaust a habox htria) (hexhaust b hbbox htrib) hab


theorem bc44_rootWardRootParent_allRankPar_false_of_farParent
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ z₀ : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hy0box : y₀ ∈ box d n) (htriy0 : IsTrifurcation d ω y₀)
    (hz0box : z₀ ∈ box d n) (htriz0 : IsTrifurcation d ω z₀)
    (hxy : x₀ ≠ y₀) (hxz : x₀ ≠ z₀) (hyz : y₀ ≠ z₀)
    (hexhaust : ∀ a, a ∈ box d n → IsTrifurcation d ω a → a = x₀ ∨ a = y₀ ∨ a = z₀)
    (hconn : Connected d ω x₀ y₀)
    (hadj : bc37_ArmAdjacent ω n y₀ z₀)
    (hfar : ¬ Connected d (removeSite y₀ ω) x₀ z₀) :
    ¬ ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
        bc43_RootWardRootParent ω n rank par := by
  intro hwalk
  set rank : Site d → ℕ ×ₗ ℕ := bc44_farWitnessRank y₀ z₀ with hrank
  set par : Site d → Site d := fun _ => z₀ with hpar
  
  have hrx : rank x₀ = toLex ((0 : ℕ), (0 : ℕ)) := by
    simp only [hrank, bc44_farWitnessRank, if_neg hxy, if_neg hxz]
  have hry : rank y₀ = toLex ((2 : ℕ), (0 : ℕ)) := by
    simp only [hrank, bc44_farWitnessRank, ↓reduceIte]
  have hrz : rank z₀ = toLex ((1 : ℕ), (0 : ℕ)) := by
    simp only [hrank, bc44_farWitnessRank, if_neg (Ne.symm hyz), ↓reduceIte]
  
  have hinj : ∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b →
      a ≠ b → Connected d ω a b → rank a ≠ rank b :=
    bc44_farWitness_rank_injective ω n hxy hxz hyz hexhaust
  
  have hlt : rank x₀ < rank y₀ := by rw [hrx, hry]; exact stt_lex_lt_fst (by norm_num)
  have hxpar : x₀ ≠ par y₀ := by simpa [hpar] using hxz
  have hprank : rank (par y₀) < rank y₀ := by
    simp only [hpar]; rw [hrz, hry]; exact stt_lex_lt_fst (by norm_num)
  have hadj' : bc37_ArmAdjacent ω n y₀ (par y₀) := by simpa [hpar] using hadj
  
  obtain ⟨p, hp⟩ :=
    hwalk rank par hinj x₀ hx0box htri0 y₀ hy0box htriy0 hxy hconn hlt hxpar
      (by simpa [hpar] using hz0box) (by simpa [hpar] using htriz0) hadj' hprank
  
  have hconn_cut : Connected d (removeSite y₀ ω) x₀ (par y₀) :=
    (bc42_avoidingWalk_iff_connected_removeSite ω hxy).mp ⟨p, hp⟩
  simp only [hpar] at hconn_cut
  exact hfar hconn_cut


end StatMech.Walls
