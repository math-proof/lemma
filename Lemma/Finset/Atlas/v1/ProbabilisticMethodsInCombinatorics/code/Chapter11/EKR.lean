import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter11.EKR
open SimpleGraph Finset Filter Real Asymptotics ErdosKleitmanRothschild


namespace ErdosKleitmanRothschild

/--
[subgraph_count_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter11/EKR.lean)
-/
@[path]
lemma subgraph_count_le
  {n : ℕ}
  {G : SimpleGraph (Fin n)}
  [DecidableRel G.Adj] :
-- imply
  Nat.card {H : SimpleGraph (Fin n) // H ≤ G} ≤ 2 ^ G.edgeFinset.card := by
-- proof
  classical
  exact (Nat.card_le_card_of_injective
    (fun (x : {H : SimpleGraph (Fin n) // H ≤ G}) =>
      (⟨x.val.edgeFinset, Finset.mem_powerset.mpr
        (edgeFinset_subset_edgeFinset.mpr x.prop)⟩ : ↥(G.edgeFinset.powerset : Finset _)))
    (by intro ⟨_, _⟩ ⟨_, _⟩ h; exact Subtype.ext (edgeFinset_inj.mp (Subtype.mk.inj h)))).trans
    (by rw [Nat.card_eq_finsetCard, Finset.card_powerset])

end ErdosKleitmanRothschild

namespace ErdosKleitmanRothschild

/--
[triangleFreeCount_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter11/EKR.lean)
-/
@[path]
lemma triangleFreeCount_upper_bound
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, triangleFreeCount n ≤ ⌈(n : ℝ) ^ (C * (n : ℝ) ^ ((3:ℝ)/2))⌉₊ * 2 ^ ⌈(1/4 + ε) * (n : ℝ) ^ 2⌉₊ := by
-- proof
  obtain ⟨C, hC_pos, hContainers⟩ :=
    ContainersTriangleFree.containers_triangle_free ε hε
  refine ⟨C, hC_pos, fun n => ?_⟩
  classical
  obtain ⟨𝒞, h_size, h_edges, h_cover⟩ := hContainers n
  have h_nat_edges : ∀ G ∈ 𝒞, G.edgeFinset.card ≤ ⌈(1/4 + ε) * (n : ℝ) ^ 2⌉₊ := by
    intro G hG
    have key : (G.edgeFinset.card : ℝ) ≤ (1/4 + ε) * (n : ℝ) ^ 2 := by convert h_edges G hG
    exact_mod_cast key.trans (Nat.le_ceil _)
  have h_nat_size : 𝒞.card ≤ ⌈(n : ℝ) ^ (C * (↑n) ^ ((3:ℝ)/2))⌉₊ := by
    have key : (𝒞.card : ℝ) ≤ (n : ℝ) ^ (C * (↑n) ^ ((3:ℝ)/2)) := h_size
    exact_mod_cast key.trans (Nat.le_ceil _)
  let f : {H : SimpleGraph (Fin n) // H.CliqueFree 3} →
    (i : ↥𝒞) × {H : SimpleGraph (Fin n) // H ≤ i.val} :=
    fun ⟨H, hH⟩ => ⟨⟨(h_cover H hH).choose, ((h_cover H hH).choose_spec).1⟩,
      ⟨H, ((h_cover H hH).choose_spec).2⟩⟩
  have hf : Function.Injective f := by
    intro ⟨H1, hH1⟩ ⟨H2, hH2⟩ heq
    simp only [f, Sigma.mk.inj_iff] at heq
    obtain ⟨heq1, heq2⟩ := heq
    rw [Subtype.heq_iff_coe_eq] at heq2
    · exact Subtype.ext heq2
    · intro a; constructor <;> intro ha
      · exact le_trans ha (by rw [Subtype.mk.injEq] at heq1; rw [heq1])
      · exact le_trans ha (by rw [Subtype.mk.injEq] at heq1; rw [← heq1])
  unfold triangleFreeCount
  calc Nat.card {H : SimpleGraph (Fin n) // H.CliqueFree 3}
    ≤ Nat.card ((i : ↥𝒞) × {H : SimpleGraph (Fin n) // H ≤ i.val}) :=
      Nat.card_le_card_of_injective f hf
    _ = ∑ i : ↥𝒞, Nat.card {H : SimpleGraph (Fin n) // H ≤ i.val} := Nat.card_sigma
    _ ≤ ∑ _ : ↥𝒞, 2 ^ ⌈(1/4 + ε) * (↑n) ^ 2⌉₊ := Finset.sum_le_sum (fun ⟨G, hG⟩ _ =>
      (subgraph_count_le n G).trans
        (Nat.pow_le_pow_right (by norm_num) (h_nat_edges G hG)))
    _ = Fintype.card ↥𝒞 * 2 ^ ⌈(1/4 + ε) * (↑n) ^ 2⌉₊ := by simp [Finset.sum_const]
    _ = 𝒞.card * 2 ^ ⌈(1/4 + ε) * (↑n) ^ 2⌉₊ := by rw [Fintype.card_coe]
    _ ≤ ⌈(↑n : ℝ) ^ (C * (↑n) ^ ((3:ℝ)/2))⌉₊ * 2 ^ ⌈(1/4 + ε) * (↑n) ^ 2⌉₊ := by
      gcongr

end ErdosKleitmanRothschild


-- created on 2026-10-23
