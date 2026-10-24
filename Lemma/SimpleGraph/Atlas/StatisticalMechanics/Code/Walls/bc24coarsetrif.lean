import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc24coarsetrif
open Set SimpleGraph MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc24_cluster_ne_of_not_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_cluster_ne_of_not_connected_eq
  {d : ℕ}
  {σ : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : ¬ Connected d σ a b) :
-- imply
  cluster d σ a ≠ cluster d σ b := by
-- proof
  apply StatMech.Walls.bc24_cluster_ne_of_not_connected h

/--
[bc24_box_merges_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_box_merges_infinite_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  cluster d (forceOpenFinset (boxEdges d n) ω) x = cluster d (forceOpenFinset (boxEdges d n) ω) y := by
-- proof
  apply StatMech.Walls.bc24_box_merges_infinite ω hx hy

/--
[bc24_arm_connected_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_arm_connected_box_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b z : Site d}
-- given
  (hb : b ∈ box d n)
  (hz : z ∈ box d n)
  (hab : Connected d ω a b) :
-- imply
  Connected d (forceOpenFinset (boxEdges d n) ω) a z := by
-- proof
  apply StatMech.Walls.bc24_arm_connected_box ω hb hz hab

/--
[bc24_armEnds_connected_through_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_armEnds_connected_through_box_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
-- given
  (hb₁ : b₁ ∈ box d n)
  (hb₂ : b₂ ∈ box d n)
  (hb₃ : b₃ ∈ box d n)
  (h₁ : Connected d ω a₁ b₁)
  (h₂ : Connected d ω a₂ b₂)
  (h₃ : Connected d ω a₃ b₃) :
-- imply
  Connected d (forceOpenFinset (boxEdges d n) ω) a₁ a₂ ∧ Connected d (forceOpenFinset (boxEdges d n) ω) a₁ a₃ ∧ Connected d (forceOpenFinset (boxEdges d n) ω) a₂ a₃ := by
-- proof
  apply StatMech.Walls.bc24_armEnds_connected_through_box ω hb₁ hb₂ hb₃ h₁ h₂ h₃

/--
[bc24_coarseTrif_armClusters_distinct_after_boxRemoval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_coarseTrif_armClusters_distinct_after_boxRemoval_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : IsCoarseTrifurcation d n ω) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (cluster d (removeSites (boxFinsetBK d n) ω) a₁).Infinite ∧ (cluster d (removeSites (boxFinsetBK d n) ω) a₂).Infinite ∧ (cluster d (removeSites (boxFinsetBK d n) ω) a₃).Infinite ∧ cluster d (removeSites (boxFinsetBK d n) ω) a₁ ≠ cluster d (removeSites (boxFinsetBK d n) ω) a₂ ∧ cluster d (removeSites (boxFinsetBK d n) ω) a₁ ≠ cluster d (removeSites (boxFinsetBK d n) ω) a₃ ∧ cluster d (removeSites (boxFinsetBK d n) ω) a₂ ≠ cluster d (removeSites (boxFinsetBK d n) ω) a₃ := by
-- proof
  apply StatMech.Walls.bc24_coarseTrif_armClusters_distinct_after_boxRemoval h

/--
[bc24_box_hub_routes_armEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_box_hub_routes_armEnds_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : IsCoarseTrifurcation d n ω) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ Connected d (forceOpenFinset (boxEdges d n) ω) a₁ a₂ ∧ Connected d (forceOpenFinset (boxEdges d n) ω) a₁ a₃ ∧ Connected d (forceOpenFinset (boxEdges d n) ω) a₂ a₃ := by
-- proof
  apply StatMech.Walls.bc24_box_hub_routes_armEnds h

/--
[bc24_box_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_box_zero_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  box d 0 = {(0 : Site d)} := by
-- proof
  apply StatMech.Walls.bc24_box_zero d

/--
[bc24_zero_mem_boxFinsetBK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_zero_mem_boxFinsetBK_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  (0 : Site d) ∈ boxFinsetBK d 0 := by
-- proof
  apply StatMech.Walls.bc24_zero_mem_boxFinsetBK d

/--
[bc24_removeSites_box_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_removeSites_box_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSites (boxFinsetBK d 0) ω = removeSite (0 : Site d) ω := by
-- proof
  apply StatMech.Walls.bc24_removeSites_box_zero ω

/--
[bc24_coarseTrif_of_canonical_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_coarseTrif_of_canonical_origin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : IsCanonicalTrifurcation d ω (0 : Site d)) :
-- imply
  IsCoarseTrifurcation d 0 ω := by
-- proof
  apply StatMech.Walls.bc24_coarseTrif_of_canonical_origin h

/--
[bc24_coarseTrif_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean)
-/
@[path]
private lemma bc24_coarseTrif_nonvacuous_eq
  {d : ℕ} :
-- imply
  ∃ ω : ConfigSpace (Sym2 (Site 2)), IsCoarseTrifurcation 2 0 ω := by
-- proof
  apply StatMech.Walls.bc24_coarseTrif_nonvacuous


-- created on 2026-10-23
