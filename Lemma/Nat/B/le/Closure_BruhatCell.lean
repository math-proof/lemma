import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
open NormalizerParabolic
open BNPair CellCover CellDisjoint SubgroupOverB


namespace Definitions
end Definitions
namespace NormalizerParabolic

/--
[B_le_closure_bruhatCell](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma B_le_closure_bruhatCell
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group} :
-- imply
  bp.B ≤ Subgroup.closure (bp.bruhatCell w) := by
-- proof
  intro b hb
  obtain ⟨n, hn⟩ := bp.π_surj w
  have hn_mem : (n : G) ∈ bp.bruhatCell w :=
    ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, hn, by simp⟩
  have hnb_mem : (n : G) * b ∈ bp.bruhatCell w :=
    ⟨⟨1, bp.B.one_mem⟩, n, ⟨b, hb⟩, hn, by simp⟩
  have hn_cl := Subgroup.subset_closure hn_mem
  have hnb_cl := Subgroup.subset_closure hnb_mem
  have : b = (n : G)⁻¹ * ((n : G) * b) := by group
  rw [this]
  exact (Subgroup.closure (bp.bruhatCell w)).mul_mem
    ((Subgroup.closure (bp.bruhatCell w)).inv_mem hn_cl) hnb_cl

end NormalizerParabolic

namespace NormalizerParabolic

/--
[bruhatCell_generators_in_subgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma bruhatCell_generators_in_subgroup
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {Q : Subgroup G}
  {w : M.Group}
-- given
  (hBwB : bp.bruhatCell w ⊆ (Q : Set G))
  (hBQ : bp.B ≤ Q) :
-- imply
  w ∈ bp.parabolicSubgroupW { s : B_idx | bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (Q : Set G) } :=
-- proof
  w_mem_parabolicW_of_cell_sub bp ax Q hBQ _ rfl w hBwB

end NormalizerParabolic

namespace NormalizerParabolic

/--
[generators_in_closure_bruhatCell](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma generators_in_closure_bruhatCell
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {w : M.Group} :
-- imply
  w ∈ bp.parabolicSubgroupW { s : B_idx | bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (Subgroup.closure (bp.bruhatCell w) : Set G) } := by
-- proof
  apply bruhatCell_generators_in_subgroup bp ax
  · exact Subgroup.subset_closure
  · exact B_le_closure_bruhatCell bp w

end NormalizerParabolic

namespace NormalizerParabolic

/--
[N_lift_in_closure_bruhatCell](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma N_lift_in_closure_bruhatCell
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group}
  {s : B_idx}
  {n : bp.N}
-- given
  (hs : bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (Subgroup.closure (bp.bruhatCell w) : Set G))
  (hn : bp.π n = M.toCoxeterSystem.simple s) :
-- imply
  (n : G) ∈ (Subgroup.closure (bp.bruhatCell w) : Set G) := by
-- proof
  apply hs
  exact ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, hn, by simp⟩

end NormalizerParabolic

namespace NormalizerParabolic

/--
[bruhatCell_sub_closure_B_conjB](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma bruhatCell_sub_closure_B_conjB
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {w : M.Group}
  {n : bp.N}
-- given
  (hn : bp.π n = w) :
-- imply
  bp.bruhatCell w ⊆ (Subgroup.closure ((bp.B : Set G) ∪ conjB bp n) : Set G) := by
-- proof
  set Q := Subgroup.closure ((bp.B : Set G) ∪ conjB bp n)
  have hBQ : bp.B ≤ Q := by
    intro b hb
    exact Subgroup.subset_closure (Set.mem_union_left _ hb)
  have hconjQ : ∀ b ∈ bp.B, (n : G)⁻¹ * b * (n : G) ∈ (Q : Set G) := by
    intro b hb
    apply Subgroup.subset_closure
    right
    exact ⟨b, hb, rfl⟩
  have hn_inv_conj : ∀ b ∈ bp.B, (n⁻¹ : bp.N) * b * ((n⁻¹ : bp.N) : G)⁻¹ ∈ (Q : Set G) := by
    intro b hb
    simp only [Subgroup.coe_inv, inv_inv]
    exact hconjQ b hb
  have hπ_inv : bp.π (n⁻¹) = w⁻¹ := by
    rw [map_inv, hn]
  have hn_inv_Q : ((n⁻¹ : bp.N) : G) ∈ (Q : Set G) :=
    N_lift_mem_subgroup_of_conj bp ax Q hBQ w⁻¹ n⁻¹ hπ_inv hn_inv_conj
  have hn_Q : (n : G) ∈ (Q : Set G) := by
    have : (n : G) = ((n⁻¹ : bp.N) : G)⁻¹ := by simp
    rw [this]
    exact Q.inv_mem hn_inv_Q
  intro g hg
  obtain ⟨⟨b₁, hb₁⟩, n', ⟨b₂, hb₂⟩, hπ', hg_eq⟩ := hg
  have hπ_diff : bp.π (n' * n⁻¹) = 1 := by
    rw [map_mul, map_inv, hπ', hn, mul_inv_cancel]
  have hdiff_T : ((n' * n⁻¹ : bp.N) : G) ∈ bp.T := (bp.π_ker _).mp hπ_diff
  have hdiff_B : ((n' * n⁻¹ : bp.N) : G) ∈ bp.B := by
    rw [bp.T_eq] at hdiff_T; exact (Subgroup.mem_inf.mp hdiff_T).1
  have hn'_Q : (n' : G) ∈ (Q : Set G) := by
    have : (n' : G) = ((n' * n⁻¹ : bp.N) : G) * (n : G) := by
      simp [Subgroup.coe_mul]
    rw [this]
    exact Q.mul_mem (hBQ hdiff_B) hn_Q
  rw [hg_eq]
  exact Q.mul_mem (Q.mul_mem (hBQ hb₁) hn'_Q) (hBQ hb₂)

end NormalizerParabolic

namespace NormalizerParabolic

/--
[closure_B_conjB_sub_closure_bruhatCell](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma closure_B_conjB_sub_closure_bruhatCell
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group}
  {n : bp.N}
-- given
  (hn : bp.π n = w) :
-- imply
  Subgroup.closure ((bp.B : Set G) ∪ conjB bp n) ≤ Subgroup.closure (bp.bruhatCell w) := by
-- proof
  rw [Subgroup.closure_le]
  intro g hg
  obtain hg_B | hg_conj := hg
  · exact B_le_closure_bruhatCell bp w hg_B
  · obtain ⟨b, hb, hg_eq⟩ := hg_conj
    rw [hg_eq]
    have hn_mem : (n : G) ∈ bp.bruhatCell w :=
      ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, hn, by simp⟩
    have hn_cl := Subgroup.subset_closure hn_mem
    have hn_inv_cl := (Subgroup.closure (bp.bruhatCell w)).inv_mem hn_cl
    have hb_cl := B_le_closure_bruhatCell bp w hb
    exact (Subgroup.closure (bp.bruhatCell w)).mul_mem
      ((Subgroup.closure (bp.bruhatCell w)).mul_mem hn_inv_cl hb_cl) hn_cl

end NormalizerParabolic

namespace NormalizerParabolic

/--
[closure_bruhatCell_eq_closure_B_conjB](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma closure_bruhatCell_eq_closure_B_conjB
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {w : M.Group}
  {n : bp.N}
-- given
  (hn : bp.π n = w) :
-- imply
  Subgroup.closure (bp.bruhatCell w) = Subgroup.closure ((bp.B : Set G) ∪ conjB bp n) := by
-- proof
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact bruhatCell_sub_closure_B_conjB bp ax w n hn
  · exact closure_B_conjB_sub_closure_bruhatCell bp w n hn

end NormalizerParabolic

/--
[B_sub_standardParabolic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma B_sub_standardParabolic_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {S' : Set B_idx} :
-- imply
  (bp.B : Set G) ⊆ bp.standardParabolic S' := by
-- proof
  apply NormalizerParabolic.B_sub_standardParabolic bp S'

/--
[standardParabolic_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma standardParabolic_mul_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {S' : Set B_idx}
  {x y : G}
-- given
  (hx : x ∈ bp.standardParabolic S')
  (hy : y ∈ bp.standardParabolic S') :
-- imply
  x * y ∈ bp.standardParabolic S' := by
-- proof
  apply NormalizerParabolic.standardParabolic_mul bp ax S' hx hy

/--
[standardParabolic_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma standardParabolic_inv_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {S' : Set B_idx}
  {x : G}
-- given
  (hx : x ∈ bp.standardParabolic S') :
-- imply
  x⁻¹ ∈ bp.standardParabolic S' := by
-- proof
  apply NormalizerParabolic.standardParabolic_inv bp S' hx

/--
[N_lift_mem_subgroup_of_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma N_lift_mem_subgroup_of_conj_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {Q : Subgroup G}
  {w : M.Group}
  {n : bp.N}
-- given
  (hBQ : bp.B ≤ Q)
  (hn : bp.π n = w)
  (hn_conj : ∀ b ∈ bp.B, (n : G) * b * (n : G)⁻¹ ∈ (Q : Set G)) :
-- imply
  (n : G) ∈ (Q : Set G) := by
-- proof
  apply NormalizerParabolic.N_lift_mem_subgroup_of_conj bp ax Q hBQ w n hn hn_conj

/--
[bruhatCell_sub_of_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma bruhatCell_sub_of_conj_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {Q : Subgroup G}
  {w : M.Group}
  {n : bp.N}
-- given
  (hBQ : bp.B ≤ Q)
  (hn : bp.π n = w)
  (hn_conj : ∀ b ∈ bp.B, (n : G) * b * (n : G)⁻¹ ∈ (Q : Set G)) :
-- imply
  bp.bruhatCell w ⊆ (Q : Set G) := by
-- proof
  apply NormalizerParabolic.bruhatCell_sub_of_conj bp ax Q hBQ w n hn hn_conj

/--
[normalizer_in_parabolic_from_bnpair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/NormalizerParabolicProof.lean)
-/
@[path]
private lemma normalizer_in_parabolic_from_bnpair_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp} :
-- imply
  ∀ S' : Set B_idx, ∀ g : G, (∀ x, x ∈ bp.standardParabolic S' ↔ g * x * g⁻¹ ∈ bp.standardParabolic S') → g ∈ bp.standardParabolic S' := by
-- proof
  apply NormalizerParabolic.normalizer_in_parabolic_from_bnpair bp ax


-- created on 2026-10-24
