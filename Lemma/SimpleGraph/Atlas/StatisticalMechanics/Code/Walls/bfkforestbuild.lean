import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bfkforestbuild
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bfk_leafClause_of_openEdgeInj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_leafClause_of_openEdgeInj_eq
  {d : ℕ}
  {W : Type}
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {edgeOf : W → Sym2 (Site d)}
-- given
  (hmem : ∀ v, G.degree v = 1 → edgeOf v ∈ F)
  (hopen : ∀ v, G.degree v = 1 → ω (edgeOf v) = true)
  (hinj : Set.InjOn edgeOf {v | G.degree v = 1}) :
-- imply
  (univ.filter (fun v => G.degree v = 1)).card ≤ bel_leafOpenCount F ω := by
-- proof
  apply StatMech.Walls.bfk_leafClause_of_openEdgeInj G F ω edgeOf hmem hopen hinj

/--
[bfk_pt_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_pt_outside_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ c H : ℤ}
-- given
  (hc : (L : ℤ) < c - m) :
-- imply
  bc57_pt c H ∉ bc61_boxAround 2 L (bc57_pt m h₀) := by
-- proof
  apply StatMech.Walls.bfk_pt_outside hc

/--
[bfk_rightArm_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_rightArm_reach_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ H : ℤ}
  {j : ℕ}
-- given
  (hH : 1 ≤ H) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines) (bc57_pt (m + (L : ℤ) + 1) H) (bc57_pt (m + (L : ℤ) + 1 + (j : ℤ)) H) := by
-- proof
  apply StatMech.Walls.bfk_rightArm_reach hH j

/--
[bfk_rightArm_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_rightArm_infinite_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ H : ℤ}
-- given
  (hH : 1 ≤ H) :
-- imply
  (cluster 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines) (bc57_pt (m + (L : ℤ) + 1) H)).Infinite := by
-- proof
  apply StatMech.Walls.bfk_rightArm_infinite hH

/--
[bfk_arm_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_arm_disconnected_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ c H H' : ℤ}
-- given
  (hne : H ≠ H') :
-- imply
  ¬ Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines) (bc57_pt c H) (bc57_pt c H') := by
-- proof
  apply StatMech.Walls.bfk_arm_disconnected hne

/--
[bfk_arm_boxAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_arm_boxAdjacent_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ H : ℤ}
-- given
  (hH : 1 ≤ H)
  (hHlo : h₀ - (L : ℤ) ≤ H)
  (hHhi : H ≤ h₀ + (L : ℤ)) :
-- imply
  ∃ b ∈ bc61_boxAround 2 L (bc57_pt m h₀), (openSubgraph 2 bc60_upperLines).Adj b (bc57_pt (m + (L : ℤ) + 1) H) := by
-- proof
  apply StatMech.Walls.bfk_arm_boxAdjacent hH hHlo hHhi

/--
[bfk_isCoarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_isCoarseTrif_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ : ℤ}
-- given
  (hL : 3 ≤ L)
  (hh₀ : 0 ≤ h₀) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (bc57_pt m h₀) := by
-- proof
  apply StatMech.Walls.bfk_isCoarseTrif hL hh₀

/--
[bfk_coarseTcount_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_coarseTcount_lower_eq
  {d : ℕ}
  {L : ℕ}
  {R : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  (R + 1) * (2 * R + 1) ≤ bc61_coarseTcount bc60_upperLines L R := by
-- proof
  apply StatMech.Walls.bfk_coarseTcount_lower hL R

/--
[bfk_boxCard_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_boxCard_le_eq
  {d : ℕ}
  {R : ℕ} :
-- imply
  (boxFinsetBK 2 R).card ≤ (2 * R + 1) * (2 * R + 1) := by
-- proof
  apply StatMech.Walls.bfk_boxCard_le R

/--
[bfk_perConfigForest_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_perConfigForest_false_eq
  {d : ℕ}
  {L : ℕ}
  {F : ℕ → Finset (Sym2 (Site 2))}
-- given
  (hL : 3 ≤ L)
  (hdens : Filter.Tendsto (fun R => ((F R).card : ℝ) / ((boxFinsetBK 2 R).card : ℝ)) Filter.atTop (nhds 0)) :
-- imply
  ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ), bpe_CoarseForestNoBnd ω L R (bel_leafOpenCount (F R) ω)) := by
-- proof
  apply StatMech.Walls.bfk_perConfigForest_false hL F hdens

/--
[bfk_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestbuild.lean)
-/
@[path]
private lemma bfk_status_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  (∀ {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] (F : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2))) (edgeOf : W → Sym2 (Site 2)), (∀ v, G.degree v = 1 → edgeOf v ∈ F) → (∀ v, G.degree v = 1 → ω (edgeOf v) = true) → Set.InjOn edgeOf {v | G.degree v = 1} → (univ.filter (fun v => G.degree v = 1)).card ≤ bel_leafOpenCount F ω) ∧ (∀ (m h₀ : ℤ), 0 ≤ h₀ → bc61_IsCoarseTrifurcation bc60_upperLines L (bc57_pt m h₀)) ∧ (∀ R, (R + 1) * (2 * R + 1) ≤ bc61_coarseTcount bc60_upperLines L R) ∧ (∀ (F : ℕ → Finset (Sym2 (Site 2))), Filter.Tendsto (fun R => ((F R).card : ℝ) / ((boxFinsetBK 2 R).card : ℝ)) Filter.atTop (nhds 0) → ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ), bpe_CoarseForestNoBnd ω L R (bel_leafOpenCount (F R) ω))) := by
-- proof
  apply StatMech.Walls.bfk_status hL


-- created on 2026-10-23
