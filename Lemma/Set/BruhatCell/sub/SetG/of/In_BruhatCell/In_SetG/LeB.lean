import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.SubgroupOverBProof
open SubgroupOverB


/--
[cell_sub_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SubgroupOverBProof.lean)
-/
@[path]
private lemma cell_sub_of_mem_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {P : Subgroup G}
  {w : M.Group}
  {g : G}
-- given
  (hBP : bp.B ≤ P)
  (hgP : g ∈ (P : Set G))
  (hgW : g ∈ bp.bruhatCell w) :
-- imply
  bp.bruhatCell w ⊆ (P : Set G) := by
-- proof
  apply SubgroupOverB.cell_sub_of_mem bp P hBP w g hgP hgW

/--
[N_rep_mem_P_of_parabolicW](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SubgroupOverBProof.lean)
-/
@[path]
private lemma N_rep_mem_P_of_parabolicW_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {P : Subgroup G}
  {S' : Set B_idx}
  {w : M.Group}
  {n : bp.N}
-- given
  (hBP : bp.B ≤ P)
  (hS' : ∀ s ∈ S', bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (P : Set G))
  (hw : w ∈ bp.parabolicSubgroupW S')
  (hn : bp.π n = w) :
-- imply
  (n : G) ∈ (P : Set G) := by
-- proof
  apply SubgroupOverB.N_rep_mem_P_of_parabolicW bp P hBP S' hS' w hw n hn

/--
[standardParabolic_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SubgroupOverBProof.lean)
-/
@[path]
private lemma standardParabolic_sub_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {P : Subgroup G}
  {S' : Set B_idx}
-- given
  (hBP : bp.B ≤ P)
  (hS' : ∀ s ∈ S', bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (P : Set G)) :
-- imply
  bp.standardParabolic S' ⊆ (P : Set G) := by
-- proof
  apply SubgroupOverB.standardParabolic_sub bp P hBP S' hS'

/--
[bn3_gives_element_in_BsB](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SubgroupOverBProof.lean)
-/
@[path]
private lemma bn3_gives_element_in_BsB_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {s : B_idx}
  {n_s : bp.N}
-- given
  (hn_s : bp.π n_s = M.toCoxeterSystem.simple s) :
-- imply
  ∃ x : G, x ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) ∧ ∃ y : G, y ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) ∧ x⁻¹ * y ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) := by
-- proof
  apply SubgroupOverB.bn3_gives_element_in_BsB bp ax s n_s hn_s

/--
[w_mem_parabolicW_of_cell_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SubgroupOverBProof.lean)
-/
@[path]
private lemma w_mem_parabolicW_of_cell_sub_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {P : Subgroup G}
  {S' : Set B_idx}
  {w : M.Group}
-- given
  (hBP : bp.B ≤ P)
  (hS'_def : S' = { s : B_idx | bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (P : Set G) })
  (hw : bp.bruhatCell w ⊆ (P : Set G)) :
-- imply
  w ∈ bp.parabolicSubgroupW S' := by
-- proof
  apply SubgroupOverB.w_mem_parabolicW_of_cell_sub bp ax P hBP S' hS'_def w hw

/--
[subgroup_over_B_eq_parabolic_from_bnpair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SubgroupOverBProof.lean)
-/
@[path]
private lemma subgroup_over_B_eq_parabolic_from_bnpair_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp} :
-- imply
  ∀ P : Subgroup G, bp.B ≤ P → ∃ S' : Set B_idx, (P : Set G) = bp.standardParabolic S' := by
-- proof
  apply SubgroupOverB.subgroup_over_B_eq_parabolic_from_bnpair bp ax


-- created on 2026-10-23
