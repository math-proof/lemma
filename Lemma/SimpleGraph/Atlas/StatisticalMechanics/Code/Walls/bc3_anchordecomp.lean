import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc3_anchordecomp.Part2
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc3_mem_anchorSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean)
-/
@[path]
private lemma bc3_mem_anchorSites_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {a : Site d} :
-- imply
  a ∈ bc3_anchorSites G ↔ ∃ e ∈ G, a ∈ e := by
-- proof
  apply StatMech.Walls.bc3_mem_anchorSites

/--
[bc3_anchorSites_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean)
-/
@[path]
private lemma bc3_anchorSites_finite_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))} :
-- imply
  (bc3_anchorSites G).Finite := by
-- proof
  apply StatMech.Walls.bc3_anchorSites_finite G

/--
[bc3_anchor_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean)
-/
@[path]
private lemma bc3_anchor_decomp_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x z : Site d}
-- given
  (h : Connected d (forceOpenFinset G ω) x z) :
-- imply
  Connected d ω x z ∨ ∃ a ∈ bc3_anchorSites G, Connected d ω a z := by
-- proof
  apply StatMech.Walls.bc3_anchor_decomp G ω x z h

/--
[bc3_cluster_covered_by_anchors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean)
-/
@[path]
private lemma bc3_cluster_covered_by_anchors_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  cluster d (forceOpenFinset G ω) x ⊆ ⋃ a ∈ insert x (bc3_anchorSites G), cluster d ω a := by
-- proof
  apply StatMech.Walls.bc3_cluster_covered_by_anchors G ω x

/--
[bc3_anchor_cover_index_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean)
-/
@[path]
private lemma bc3_anchor_cover_index_finite_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {x : Site d} :
-- imply
  (insert x (bc3_anchorSites G)).Finite := by
-- proof
  apply StatMech.Walls.bc3_anchor_cover_index_finite G x

/--
[bc3_corridorUnion_eq_pairwiseSeparated_wiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean)
-/
@[path]
private lemma bc3_corridorUnion_eq_pairwiseSeparated_wiring_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ} :
-- imply
  bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ ↔ (¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω)) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) ∧ ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω)) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) ∧ ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω)) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) := by
-- proof
  apply StatMech.Walls.bc3_corridorUnion_eq_pairwiseSeparated_wiring ω j₁ j₂ j₃ L₁ L₂ L₃

/--
[bc3_anchor_decomp_corridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean)
-/
@[path]
private lemma bc3_anchor_decomp_corridor_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x z : Site d}
-- given
  (h : Connected d (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω) x z) :
-- imply
  Connected d ω x z ∨ ∃ a ∈ bc3_anchorSites (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃), Connected d ω a z := by
-- proof
  apply StatMech.Walls.bc3_anchor_decomp_corridor j₁ j₂ j₃ L₁ L₂ L₃ ω x z h

/--
[bc3_origin_mem_anchorSites_corridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean)
-/
@[path]
private lemma bc3_origin_mem_anchorSites_corridor_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  (0 : Site d) ∈ bc3_anchorSites (hrHD_corridorEdges j (L + 1)) := by
-- proof
  apply StatMech.Walls.bc3_origin_mem_anchorSites_corridor j L

/--
[bc3_rayPt_mem_anchorSites_corridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean)
-/
@[path]
private lemma bc3_rayPt_mem_anchorSites_corridor_eq
  {d : ℕ}
  {j : Fin d}
  {L t : ℕ}
-- given
  (ht : t < L) :
-- imply
  hrHD_rayPt j ((t : ℤ) + 1) ∈ bc3_anchorSites (hrHD_corridorEdges j L) := by
-- proof
  apply StatMech.Walls.bc3_rayPt_mem_anchorSites_corridor j L t ht

/--
[bc3_anchorSites_corridorUnion_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean)
-/
@[path]
private lemma bc3_anchorSites_corridorUnion_nonempty_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ} :
-- imply
  (bc3_anchorSites (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃)).Nonempty := by
-- proof
  apply StatMech.Walls.bc3_anchorSites_corridorUnion_nonempty j₁ j₂ j₃ L₁ L₂ L₃


-- created on 2026-10-23
