import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bgeexploration.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bge_cluster_disjoint_of_notConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgeexploration.lean)
-/
@[path]
private lemma bge_cluster_disjoint_of_notConnected_eq
  {d : ℕ}
  {ω' : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : ¬ Connected d ω' a b) :
-- imply
  Disjoint (cluster d ω' a) (cluster d ω' b) := by
-- proof
  apply StatMech.Walls.bge_cluster_disjoint_of_notConnected h

/--
[bge_singleGenuineTrif_arms_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgeexploration.lean)
-/
@[path]
private lemma bge_singleGenuineTrif_arms_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {a₁ a₂ a₃ : Site d}
-- given
  (hsep : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) :
-- imply
  Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₁) (cluster d (removeSites (bc61_boxAround d L y) ω) a₂) ∧ Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₁) (cluster d (removeSites (bc61_boxAround d L y) ω) a₃) ∧ Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₂) (cluster d (removeSites (bc61_boxAround d L y) ω) a₃) := by
-- proof
  apply StatMech.Walls.bge_singleGenuineTrif_arms_disjoint hsep

/--
[bge_exploration_of_singleGenuineTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgeexploration.lean)
-/
@[path]
private lemma bge_exploration_of_singleGenuineTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d}
-- given
  (hy : btr_IsGenuineCoarseTrif ω L y)
  (huniq : ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y)
  (hbdry : ∀ a : Site d, (∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a) → Connected d ω y a → (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → (cluster d (removeSites (bc61_boxAround d L y) ω) a ∩ vertexBoundary d R).Nonempty) :
-- imply
  bfg_GenuineExploration ω L R := by
-- proof
  apply StatMech.Walls.bge_exploration_of_singleGenuineTrif ω L R y hy huniq hbdry

/--
[bge_exploration_of_armComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgeexploration.lean)
-/
@[path]
private lemma bge_exploration_of_armComponents_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (h : bge_ArmComponents ω L R) :
-- imply
  bfg_GenuineExploration ω L R := by
-- proof
  apply StatMech.Walls.bge_exploration_of_armComponents ω L R hz₀ hz₁ hzne h

/--
[bge_exploration_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgeexploration.lean)
-/
@[path]
private lemma bge_exploration_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ btr_IsGenuineCoarseTrif ω L y) :
-- imply
  bfg_GenuineExploration ω L R := by
-- proof
  apply StatMech.Walls.bge_exploration_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bge_bc60_exploration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgeexploration.lean)
-/
@[path]
private lemma bge_bc60_exploration_eq
  {d : ℕ}
  {L R : ℕ}
  {z₀ z₁ : Site 2}
-- given
  (hz₀ : z₀ ∈ vertexBoundary 2 R)
  (hz₁ : z₁ ∈ vertexBoundary 2 R)
  (hzne : z₀ ≠ z₁) :
-- imply
  bfg_GenuineExploration bc60_upperLines L R := by
-- proof
  apply StatMech.Walls.bge_bc60_exploration L R hz₀ hz₁ hzne

/--
[bge_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgeexploration.lean)
-/
@[path]
private lemma bge_status_eq
  {d : ℕ} :
-- imply
  (∀ {ω : ConfigSpace (Sym2 (Site d))} {L : ℕ} {y a₁ a₂ a₃ : Site d}, (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) → Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₁) (cluster d (removeSites (bc61_boxAround d L y) ω) a₂)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (y : Site d), btr_IsGenuineCoarseTrif ω L y → (∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y) → (∀ a : Site d, (∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a) → Connected d ω y a → (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → (cluster d (removeSites (bc61_boxAround d L y) ω) a ∩ vertexBoundary d R).Nonempty) → bfg_GenuineExploration ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → bge_ArmComponents ω L R → bfg_GenuineExploration ω L R) := by
-- proof
  apply StatMech.Walls.bge_status


-- created on 2026-10-23
