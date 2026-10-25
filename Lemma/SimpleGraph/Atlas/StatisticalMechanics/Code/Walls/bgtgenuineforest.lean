import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bgtgenuineforest.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bgt_mem_genuineTrifFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean)
-/
@[path]
private lemma bgt_mem_genuineTrifFinset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d} :
-- imply
  y ∈ btr_genuineTrifFinset ω L R ↔ y ∈ box d R ∧ btr_IsGenuineCoarseTrif ω L y := by
-- proof
  apply StatMech.Walls.bgt_mem_genuineTrifFinset ω L R y

/--
[bgt_genuineTcount_le_leafCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean)
-/
@[path]
private lemma bgt_genuineTcount_le_leafCard_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R m : ℕ}
-- given
  (h : bgt_GenuineForestNoBnd ω L R m) :
-- imply
  (btr_genuineTrifFinset ω L R).card ≤ m := by
-- proof
  apply StatMech.Walls.bgt_genuineTcount_le_leafCard ω L R m h

/--
[bgt_genuineForest_imp_noBnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean)
-/
@[path]
private lemma bgt_genuineForest_imp_noBnd_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bgt_GenuineForest ω L R) :
-- imply
  bgt_GenuineForestNoBnd ω L R (boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bgt_genuineForest_imp_noBnd ω L R h

/--
[bgt_genuineTcount_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean)
-/
@[path]
private lemma bgt_genuineTcount_le_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bgt_GenuineForest ω L R) :
-- imply
  (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bgt_genuineTcount_le_boundary ω L R h

/--
[bgt_genuineForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean)
-/
@[path]
private lemma bgt_genuineForest_of_noTrif_eq
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
  bgt_GenuineForest ω L R := by
-- proof
  apply StatMech.Walls.bgt_genuineForest_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bgt_bc60_genuineForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean)
-/
@[path]
private lemma bgt_bc60_genuineForest_eq
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
  apply StatMech.Walls.bgt_bc60_genuineForest L R hz₀ hz₁ hzne

/--
[bgt_bc60_genuineTcount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean)
-/
@[path]
private lemma bgt_bc60_genuineTcount_zero_eq
  {d : ℕ}
  {L R : ℕ} :
-- imply
  (btr_genuineTrifFinset bc60_upperLines L R).card = 0 := by
-- proof
  apply StatMech.Walls.bgt_bc60_genuineTcount_zero L R

/--
[bgt_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean)
-/
@[path]
private lemma bgt_status_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bgt_GenuineForest ω L R → (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R m : ℕ), bgt_GenuineForestNoBnd ω L R m → (btr_genuineTrifFinset ω L R).card ≤ m) ∧ (∀ (L R : ℕ), (btr_genuineTrifFinset bc60_upperLines L R).card = 0) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → (∀ y, y ∈ box d R → ¬ btr_IsGenuineCoarseTrif ω L y) → bgt_GenuineForest ω L R) := by
-- proof
  apply StatMech.Walls.bgt_status hd


-- created on 2026-10-23
