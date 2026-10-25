import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc2_corridorChain_in_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean)
-/
@[path]
private lemma bc2_corridorChain_in_union_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {G : Finset (Sym2 (Site d))}
-- given
  (hsub : hrHD_corridorEdges j (L + 1) ⊆ G) :
-- imply
  Relation.ReflTransGen (CorridorStep G) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc2_corridorChain_in_union j L G hsub

/--
[bc2_csc_of_forcedCorridorRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean)
-/
@[path]
private lemma bc2_csc_of_forcedCorridorRouting_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc2_ForcedCorridorRouting ω) :
-- imply
  csc_DistinctClusterCorridors ω := by
-- proof
  apply StatMech.Walls.bc2_csc_of_forcedCorridorRouting ω h

/--
[bc2_corridorCover_of_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean)
-/
@[path]
private lemma bc2_corridorCover_of_box_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc2_BoxForcedCorridorRouting d n) :
-- imply
  threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), CorridorWorks a₁ a₂ a₃ G := by
-- proof
  apply StatMech.Walls.bc2_corridorCover_of_box h

/--
[bc2_burtonKeane_uniqueness_of_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean)
-/
@[path]
private lemma bc2_burtonKeane_uniqueness_of_box_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hroute : ∀ n : ℕ, bc2_BoxForcedCorridorRouting d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc2_burtonKeane_uniqueness_of_box μ herg hfe bdry hbound hvol hdens hroute

/--
[bc2_pairwiseSeparated_zero_of_cutDisconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean)
-/
@[path]
private lemma bc2_pairwiseSeparated_zero_of_cutDisconnected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hsep12 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
  (hsep13 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
  (hsep23 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
-- imply
  bc2_PairwiseSeparated ω j₁ j₂ j₃ 0 0 0 := by
-- proof
  apply StatMech.Walls.bc2_pairwiseSeparated_zero_of_cutDisconnected ω j₁ j₂ j₃ hsep12 hsep13 hsep23

/--
[bc2_forcedCorridorRouting_of_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean)
-/
@[path]
private lemma bc2_forcedCorridorRouting_of_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃)
  (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite)
  (hsep12 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
  (hsep13 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
  (hsep23 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
-- imply
  bc2_ForcedCorridorRouting ω := by
-- proof
  apply StatMech.Walls.bc2_forcedCorridorRouting_of_neighbour_witnesses ω hj12 hj13 hj23 hi1 hi2 hi3 hsep12 hsep13 hsep23

/--
[bc2_csc_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean)
-/
@[path]
private lemma bc2_csc_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃)
  (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite)
  (hsep12 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
  (hsep13 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
  (hsep23 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
-- imply
  csc_DistinctClusterCorridors ω := by
-- proof
  apply StatMech.Walls.bc2_csc_neighbour_witnesses ω hj12 hj13 hj23 hi1 hi2 hi3 hsep12 hsep13 hsep23

/--
[bc2_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean)
-/
@[path]
private lemma bc2_core_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  (bc2_BoxForcedCorridorRouting d n → threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), CorridorWorks a₁ a₂ a₃ G) ∧ (∀ {j₁ j₂ j₃ : Fin d} (ω : ConfigSpace (Sym2 (Site d))), j₁ ≠ j₂ → j₁ ≠ j₃ → j₂ ≠ j₃ → (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite → (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite → (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite → ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) → ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) → ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) → csc_DistinctClusterCorridors ω) := by
-- proof
  apply StatMech.Walls.bc2_core n


-- created on 2026-10-23
