import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bfggenuinecarrier.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bfg_leafSel_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfggenuinecarrier.lean)
-/
@[path]
private lemma bfg_leafSel_mem_eq
  {d : ℕ}
  {comp : W → Set (Site d)}
  {R : ℕ}
  {v : W}
-- given
  (h : (comp v ∩ vertexBoundary d R).Nonempty) :
-- imply
  bfg_leafSel comp R v ∈ comp v ∩ vertexBoundary d R := by
-- proof
  apply StatMech.Walls.bfg_leafSel_mem comp R h

/--
[bfg_leafSel_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfggenuinecarrier.lean)
-/
@[path]
private lemma bfg_leafSel_injOn_eq
  {d : ℕ}
  {S : Set W}
  {comp : W → Set (Site d)}
  {R : ℕ}
-- given
  (hne : ∀ v ∈ S, (comp v ∩ vertexBoundary d R).Nonempty)
  (hdisj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Disjoint (comp u) (comp v)) :
-- imply
  Set.InjOn (bfg_leafSel comp R) S := by
-- proof
  apply StatMech.Walls.bfg_leafSel_injOn comp R hne hdisj

/--
[bfg_genuineForest_of_exploration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfggenuinecarrier.lean)
-/
@[path]
private lemma bfg_genuineForest_of_exploration_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bfg_GenuineExploration ω L R) :
-- imply
  bgt_GenuineForest ω L R := by
-- proof
  apply StatMech.Walls.bfg_genuineForest_of_exploration ω L R h

/--
[bfg_genuineTcount_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfggenuinecarrier.lean)
-/
@[path]
private lemma bfg_genuineTcount_le_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bfg_GenuineExploration ω L R) :
-- imply
  (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bfg_genuineTcount_le_boundary ω L R h

/--
[bfg_exploration_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfggenuinecarrier.lean)
-/
@[path]
private lemma bfg_exploration_of_noTrif_eq
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
  apply StatMech.Walls.bfg_exploration_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bfg_bc60_exploration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfggenuinecarrier.lean)
-/
@[path]
private lemma bfg_bc60_exploration_eq
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
  apply StatMech.Walls.bfg_bc60_exploration L R hz₀ hz₁ hzne

/--
[bfg_bc60_genuineForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfggenuinecarrier.lean)
-/
@[path]
private lemma bfg_bc60_genuineForest_eq
  {d : ℕ}
  {L R : ℕ}
  {z₀ z₁ : Site 2}
-- given
  (hz₀ : z₀ ∈ vertexBoundary 2 R)
  (hz₁ : z₁ ∈ vertexBoundary 2 R)
  (hzne : z₀ ≠ z₁) :
-- imply
  bgt_GenuineForest bc60_upperLines L R := by
-- proof
  apply StatMech.Walls.bfg_bc60_genuineForest L R hz₀ hz₁ hzne

/--
[bfg_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfggenuinecarrier.lean)
-/
@[path]
private lemma bfg_status_eq
  {d : ℕ} :
-- imply
  (∀ {W : Type} {S : Set W} (comp : W → Set (Site d)) (R : ℕ), (∀ v ∈ S, (comp v ∩ vertexBoundary d R).Nonempty) → (∀ u ∈ S, ∀ v ∈ S, u ≠ v → Disjoint (comp u) (comp v)) → Set.InjOn (bfg_leafSel comp R) S) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bfg_GenuineExploration ω L R → bgt_GenuineForest ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bfg_GenuineExploration ω L R → (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → (∀ y, y ∈ box d R → ¬ btr_IsGenuineCoarseTrif ω L y) → bfg_GenuineExploration ω L R) := by
-- proof
  apply StatMech.Walls.bfg_status


-- created on 2026-10-23
