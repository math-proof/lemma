import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.KeyLemmaBSG
open Finset in BSG


/--
[BSG.min_degree_of_dense_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/KeyLemmaBSG.lean)
-/
@[path]
lemma BSG.min_degree_of_dense_subset
  [DecidableEq α]
  [DecidableEq β]
  {A : Finset α}
  {B : Finset β}
  {X : Finset (α × β)}
  {K : ℝ}
  {ε : ℝ}
  {A' : Finset α}
-- given
  (_hX_sub : X ⊆ A ×ˢ B)
  (_hK : K ≥ 1)
  (_hX_dense : (X.card : ℝ) ≥ K⁻¹ * A.card * B.card)
  (_hε : ε > 0)
  (_hA'_sub : A' ⊆ A)
  (_hA'_card : (A'.card : ℝ) ≥ (1/4) * K⁻¹ * A.card)
  (hA'_deg : ∀ a ∈ A', ((BSG.neighbors' X a B).card : ℝ) ≥ (1/10) * K⁻¹ * B.card)
  (_hA'_bad : ∀ a ∈ A', ((A'.filter fun a₂ => (BSG.pathCount₂ B X a a₂ : ℝ) < ε * K⁻¹ ^ 2 * B.card).card : ℝ) ≤ 10 * ε * A'.card) :
-- imply
  ∀ a ∈ A', ((BSG.neighbors' X a B).card : ℝ) ≥ (1/10) * K⁻¹ * B.card :=
-- proof
  hA'_deg
namespace BSG
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

namespace BSG

/--
[exists_zpow_neg_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/KeyLemmaBSG.lean)
-/
@[path]
lemma exists_zpow_neg_le
  [DecidableEq α]
  [DecidableEq β]
  {K : ℝ}
  {r : ℝ}
-- given
  (hK : K > 1)
  (hr : r > 0) :
-- imply
  ∃ c : ℕ, K ^ (-(c : ℤ)) ≤ r := by
-- proof
  have hKinv : K⁻¹ < 1 := inv_lt_one_of_one_lt₀ hK
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hKinv
  refine ⟨n, ?_⟩
  rw [zpow_neg, zpow_natCast, show (K ^ n)⁻¹ = K⁻¹ ^ n from (inv_pow K n).symm]
  exact le_of_lt hn

end BSG

namespace BSG

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
/--
[pathCount₃_ge_of_many_good](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/KeyLemmaBSG.lean)
-/
@[path]
to `b` and each sharing at least `t` common neighbours with `a` in `B`, then the number of
length-3 paths from `a` to `b` is at least `|S| · t`. -/
lemma pathCount₃_ge_of_many_good (A : Finset α) (B : Finset β) (X : Finset (α × β))
  (a : α) (b : β) (S : Finset α) (t : ℕ)
  (hS_sub_A : S ⊆ A) (hS_conn_b : ∀ a₁ ∈ S, (a₁, b) ∈ X)
  (hS_paths : ∀ a₁ ∈ S, pathCount₂ B X a a₁ ≥ t) :
  pathCount₃ A B X a b ≥ S.card * t := by
  unfold pathCount₃ pathCount₂ at *
  let T := fun (a₁ : α) =>
    (B.filter fun b₁ => (a, b₁) ∈ X ∧ (a₁, b₁) ∈ X).image (fun b₁ => (b₁, a₁))
  have h_sub : S.biUnion T ⊆ (B ×ˢ A).filter fun p =>
    (a, p.1) ∈ X ∧ (p.2, p.1) ∈ X ∧ (p.2, b) ∈ X := by
    intro ⟨b₁, a₁⟩ hmem
    simp only [T, mem_biUnion, mem_image, mem_filter, Prod.mk.injEq] at hmem
    obtain ⟨a₁', ha₁'S, b₁', ⟨hb₁'B, hab₁', ha₁'b₁'⟩, heq⟩ := hmem
    obtain ⟨rfl, rfl⟩ := heq
    simp only [mem_filter, Finset.mem_product]
    exact ⟨⟨hb₁'B, hS_sub_A ha₁'S⟩, hab₁', ha₁'b₁', hS_conn_b a₁' ha₁'S⟩
  have h_pw : (↑S : Set α).PairwiseDisjoint T := by
    intro a₁ _ a₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [T, mem_image, mem_filter] at hp1 hp2
    obtain ⟨_, _, h1⟩ := hp1
    obtain ⟨_, _, h2⟩ := hp2
    have ha1 : a₁ = p.2 := by simp [← h1]
    have ha2 : a₂ = p.2 := by simp [← h2]
    exact hne (ha1.trans ha2.symm)
  have h_card_each : ∀ a₁ ∈ S, (T a₁).card ≥ t := by
    intro a₁ ha₁
    simp only [T]
    rw [card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1)]
    exact hS_paths a₁ ha₁
  calc ((B ×ˢ A).filter fun p =>
    (a, p.1) ∈ X ∧ (p.2, p.1) ∈ X ∧ (p.2, b) ∈ X).card
    ≥ (S.biUnion T).card := card_le_card h_sub
    _ = ∑ a₁ ∈ S, (T a₁).card := card_biUnion h_pw
    _ ≥ ∑ _a₁ ∈ S, t := Finset.sum_le_sum fun a₁ ha₁ => h_card_each a₁ ha₁
    _ = S.card * t := by simp [Finset.sum_const, smul_eq_mul]

end BSG

namespace BSG

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
/--
[pathCount₃_of_complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/KeyLemmaBSG.lean)
-/
@[path]
any `a ∈ A` and `b ∈ B` is exactly `|B| · |A|`. -/
lemma pathCount₃_of_complete (A : Finset α) (B : Finset β)
  (a : α) (b : β) (ha : a ∈ A) (hb : b ∈ B) :
  pathCount₃ A B (A ×ˢ B) a b = B.card * A.card := by
  unfold pathCount₃
  have h_eq : (B ×ˢ A).filter (fun p : β × α =>
    (a, p.1) ∈ A ×ˢ B ∧ (p.2, p.1) ∈ A ×ˢ B ∧ (p.2, b) ∈ A ×ˢ B) = B ×ˢ A := by
    ext ⟨b₁, a₁⟩
    simp only [mem_filter, Finset.mem_product]
    exact ⟨fun ⟨h, _⟩ => h, fun ⟨hb₁, ha₁⟩ =>
      ⟨⟨hb₁, ha₁⟩, ⟨ha, hb₁⟩, ⟨ha₁, hb₁⟩, ⟨ha₁, hb⟩⟩⟩
  rw [h_eq, card_product]

end BSG

/--
[BSG.density_bound_of_good_sets](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/KeyLemmaBSG.lean)
-/
@[path]
lemma BSG.density_bound_of_good_sets
  [DecidableEq α]
  [DecidableEq β]
  {A : Finset α}
  {B : Finset β}
  {X : Finset (α × β)}
  {K : ℝ}
  {A' : Finset α}
  {ε : ℝ}
  {B' : Finset β}
-- given
  (hX_sub : X ⊆ A ×ˢ B)
  (hK_gt : K > 1)
  (hA'_sub : A' ⊆ A)
  (hA'_card : (A'.card : ℝ) ≥ 1/4 * K⁻¹ * A.card)
  (hA'_deg : ∀ a ∈ A', ((BSG.neighbors' X a B).card : ℝ) ≥ 1/10 * K⁻¹ * B.card)
  (hε_pos : ε > 0)
  (hε_def : ε = 10⁻¹ ^ 6 * K⁻¹ ^ 2)
  (hB'_def : B' = B.filter (fun b => ((BSG.coNeighbors X b A').card : ℝ) > 20 * ε * A'.card)) :
-- imply
  ((X.filter (fun p => p.1 ∈ A' ∧ p.2 ∈ B')).card : ℝ) ≥ 1/80 * K⁻¹ ^ 2 * A.card * B.card := by
-- proof
  have hKinv_pos : (0 : ℝ) < K⁻¹ := inv_pos.mpr (by linarith)
  have hKinv_lt_one : K⁻¹ < 1 := inv_lt_one_of_one_lt₀ hK_gt
  have h_XA'B_lower : ((X.filter (fun p => p.1 ∈ A')).card : ℝ) ≥
    (A'.card : ℝ) * (1/10 * K⁻¹ * B.card) := by
    have h_eq : X.filter (fun p => p.1 ∈ A') =
      A'.biUnion (fun a => (BSG.neighbors' X a B).image (fun b => (a, b))) := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_biUnion, mem_image, BSG.neighbors', Prod.mk.injEq]
      constructor
      · intro ⟨hX, hA'⟩
        exact ⟨a, hA', b, ⟨(mem_product.mp (hX_sub hX)).2, hX⟩, rfl, rfl⟩
      · intro ⟨a', ha', b', ⟨_, hab'⟩, ha_eq, hb_eq⟩
        subst ha_eq; subst hb_eq
        exact ⟨hab', ha'⟩
    have h_disj : (A' : Set α).PairwiseDisjoint
      (fun a => (BSG.neighbors' X a B).image (fun b => (a, b))) := by
      intro a₁ _ a₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro ⟨x, y⟩ h1 h2
      simp only [mem_image, BSG.neighbors', mem_filter, Prod.mk.injEq] at h1 h2
      obtain ⟨_, _, ha1, _⟩ := h1
      obtain ⟨_, _, ha2, _⟩ := h2
      exact hne (ha1 ▸ ha2 ▸ rfl)
    have h_card_sum : (X.filter (fun p => p.1 ∈ A')).card =
      ∑ a ∈ A', (BSG.neighbors' X a B).card := by
      rw [h_eq, card_biUnion h_disj]
      congr 1; ext a
      exact card_image_of_injective _ (fun b₁ b₂ h => (Prod.mk.inj h).2)
    have h_sum_ge : (∑ a ∈ A', (BSG.neighbors' X a B).card : ℝ) ≥
      A'.card * (1/10 * K⁻¹ * B.card) := by
      have h := Finset.sum_le_sum (fun a (ha : a ∈ A') => hA'_deg a ha)
      rw [Finset.sum_const, nsmul_eq_mul] at h; linarith
    linarith [show ((X.filter (fun p => p.1 ∈ A')).card : ℝ) =
      (∑ a ∈ A', (BSG.neighbors' X a B).card : ℝ) from by exact_mod_cast h_card_sum]
  have h_XA'notB'_upper : ((X.filter (fun p => p.1 ∈ A' ∧ p.2 ∉ B')).card : ℝ) ≤
    (B.card : ℝ) * (20 * ε * A'.card) := by
    have h_not_B' : ∀ b ∈ B, b ∉ B' →
      ((BSG.coNeighbors X b A').card : ℝ) ≤ 20 * ε * A'.card := by
      intro b hbB hb_not
      rw [hB'_def] at hb_not
      simp only [mem_filter, not_and, not_lt] at hb_not
      exact hb_not hbB
    have h_sub : X.filter (fun p => p.1 ∈ A' ∧ p.2 ∉ B') ⊆
      (B \ B').biUnion (fun b => (BSG.coNeighbors X b A').image (fun a => (a, b))) := by
      intro ⟨a, b⟩ hp
      simp only [mem_filter] at hp
      obtain ⟨hX, hA', hnotB'⟩ := hp
      simp only [mem_biUnion, mem_sdiff, mem_image, BSG.coNeighbors, Prod.mk.injEq]
      exact ⟨b, ⟨(mem_product.mp (hX_sub hX)).2, hnotB'⟩, a,
        ⟨mem_filter.mpr ⟨hA', hX⟩, rfl, rfl⟩⟩
    have h_le_sum : (X.filter (fun p => p.1 ∈ A' ∧ p.2 ∉ B')).card ≤
      ∑ b ∈ B \ B', ((BSG.coNeighbors X b A').image (fun a => (a, b))).card :=
      (card_le_card h_sub).trans card_biUnion_le
    have h_sum_le : (∑ b ∈ B \ B', (BSG.coNeighbors X b A').card : ℝ) ≤
      ((B \ B').card : ℝ) * (20 * ε * A'.card) := by
      have h := Finset.sum_le_sum (fun b (hb : b ∈ B \ B') =>
        h_not_B' b (mem_sdiff.mp hb).1 (mem_sdiff.mp hb).2)
      rw [Finset.sum_const, nsmul_eq_mul] at h; linarith
    have hε_nn : (20 : ℝ) * ε * (A'.card : ℝ) ≥ 0 := by positivity
    have h_sdiff : ((B \ B').card : ℝ) ≤ (B.card : ℝ) :=
      Nat.cast_le.mpr (card_le_card sdiff_subset)
    calc ((X.filter (fun p => p.1 ∈ A' ∧ p.2 ∉ B')).card : ℝ)
      ≤ (∑ b ∈ B \ B', ((BSG.coNeighbors X b A').image (fun a => (a, b))).card : ℝ) := by
        exact_mod_cast h_le_sum
      _ ≤ (∑ b ∈ B \ B', (BSG.coNeighbors X b A').card : ℝ) :=
        Finset.sum_le_sum (fun b _ => Nat.cast_le.mpr card_image_le)
      _ ≤ ((B \ B').card : ℝ) * (20 * ε * A'.card) := h_sum_le
      _ ≤ (B.card : ℝ) * (20 * ε * A'.card) := by nlinarith
  have h_split : ((X.filter (fun p => p.1 ∈ A')).card : ℝ) =
    ((X.filter (fun p => p.1 ∈ A' ∧ p.2 ∈ B')).card : ℝ) +
    ((X.filter (fun p => p.1 ∈ A' ∧ p.2 ∉ B')).card : ℝ) := by
    have h_union : X.filter (fun p => p.1 ∈ A') =
      (X.filter (fun p => p.1 ∈ A' ∧ p.2 ∈ B')) ∪
      (X.filter (fun p => p.1 ∈ A' ∧ p.2 ∉ B')) := by
      ext p; simp only [mem_filter, mem_union]; tauto
    have h_disj : Disjoint
      (X.filter (fun p => p.1 ∈ A' ∧ p.2 ∈ B'))
      (X.filter (fun p => p.1 ∈ A' ∧ p.2 ∉ B')) := by
      rw [Finset.disjoint_filter]
      intro p _ ⟨_, h1⟩ ⟨_, h2⟩; exact h2 h1
    exact_mod_cast show (X.filter (fun p => p.1 ∈ A')).card =
      (X.filter (fun p => p.1 ∈ A' ∧ p.2 ∈ B')).card +
      (X.filter (fun p => p.1 ∈ A' ∧ p.2 ∉ B')).card from by
      rw [h_union, card_union_of_disjoint h_disj]
  have h_intermediate : ((X.filter (fun p => p.1 ∈ A' ∧ p.2 ∈ B')).card : ℝ) ≥
    (A'.card : ℝ) * (B.card : ℝ) * (1/10 * K⁻¹ - 20 * ε) := by
    nlinarith [show (A'.card : ℝ) * (1/10 * K⁻¹ * B.card) - B.card * (20 * ε * A'.card) =
      (A'.card : ℝ) * B.card * (1/10 * K⁻¹ - 20 * ε) from by ring]
  have h_arith : (1 : ℝ)/10 * K⁻¹ - 20 * ε ≥ 1/20 * K⁻¹ := by
    subst hε_def
    nlinarith [sq_nonneg (K⁻¹ : ℝ), mul_pos hKinv_pos hKinv_pos]
  have h_final : (A'.card : ℝ) * B.card * (1/20 * K⁻¹) ≥ 1/80 * K⁻¹ ^ 2 * A.card * B.card := by
    have h : (1/4 * K⁻¹ * (A.card : ℝ)) * B.card * (1/20 * K⁻¹) =
      1/80 * K⁻¹ ^ 2 * A.card * B.card := by ring
    have hBK : (B.card : ℝ) * (1/20 * K⁻¹) ≥ 0 := by positivity
    nlinarith
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (A'.card : ℝ) from Nat.cast_nonneg _)
    (show (0 : ℝ) ≤ (B.card : ℝ) from Nat.cast_nonneg _)]

/--
[BSG.path_count_bound_of_good_sets](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/KeyLemmaBSG.lean)
-/
@[path]
lemma BSG.path_count_bound_of_good_sets
  [DecidableEq α]
  [DecidableEq β]
  {A : Finset α}
  {B : Finset β}
  {X : Finset (α × β)}
  {K : ℝ}
  {A' : Finset α}
  {ε : ℝ}
  {B' : Finset β}
  {a : α}
  {b : β}
-- given
  (hX_sub : X ⊆ A ×ˢ B)
  (hK_gt : K > 1)
  (hA'_sub : A' ⊆ A)
  (hA'_card : (A'.card : ℝ) ≥ 1/4 * K⁻¹ * A.card)
  (hε_pos : ε > 0)
  (hA'_bad : ∀ a ∈ A', ((A'.filter fun a₂ => (BSG.pathCount₂ B X a a₂ : ℝ) < ε * K⁻¹ ^ 2 * B.card).card : ℝ) ≤ 10 * ε * A'.card)
  (hB'_def : B' = B.filter (fun b => ((BSG.coNeighbors X b A').card : ℝ) > 20 * ε * A'.card))
  (ha : a ∈ A')
  (hb : b ∈ B') :
-- imply
  (BSG.pathCount₃ A B X a b : ℝ) ≥ 10/4 * ε ^ 2 * K⁻¹ ^ 2 * (1/4) * K⁻¹ * A.card * B.card := by
-- proof
  set badSet := A'.filter fun a₂ => (BSG.pathCount₂ B X a a₂ : ℝ) < ε * K⁻¹ ^ 2 * B.card
  set S := (BSG.coNeighbors X b A') \ badSet
  have hcoN_sub_A' : BSG.coNeighbors X b A' ⊆ A' := filter_subset _ _
  have hS_sub_A : S ⊆ A := (sdiff_subset.trans hcoN_sub_A').trans hA'_sub
  have hS_conn_b : ∀ a₁ ∈ S, (a₁, b) ∈ X :=
    fun a₁ ha₁ => (mem_filter.mp ((mem_sdiff.mp ha₁).1)).2
  have hS_not_bad : ∀ a₁ ∈ S, (BSG.pathCount₂ B X a a₁ : ℝ) ≥ ε * K⁻¹ ^ 2 * B.card := by
    intro a₁ ha₁
    have hmem := mem_sdiff.mp ha₁
    have h_in_A' : a₁ ∈ A' := hcoN_sub_A' hmem.1
    have h_not_in_bad : a₁ ∉ badSet := hmem.2
    simp only [badSet, mem_filter, not_and, not_lt] at h_not_in_bad
    exact h_not_in_bad h_in_A'
  have hb_coN : ((BSG.coNeighbors X b A').card : ℝ) > 20 * ε * A'.card := by
    rw [hB'_def] at hb; exact (mem_filter.mp hb).2
  have hbad_card : (badSet.card : ℝ) ≤ 10 * ε * A'.card := hA'_bad a ha
  have hS_card : (S.card : ℝ) > 10 * ε * A'.card := by
    have h1 : (S.card : ℝ) ≥ ((BSG.coNeighbors X b A').card : ℝ) - (badSet.card : ℝ) := by
      have hi : (BSG.coNeighbors X b A' ∩ badSet).card ≤ badSet.card :=
        card_le_card inter_subset_right
      have h2 := card_sdiff_add_card_inter (BSG.coNeighbors X b A') badSet
      linarith [show ((S).card : ℝ) + ((BSG.coNeighbors X b A' ∩ badSet).card : ℝ) =
        ((BSG.coNeighbors X b A').card : ℝ) from by exact_mod_cast h2,
        show ((BSG.coNeighbors X b A' ∩ badSet).card : ℝ) ≤ (badSet.card : ℝ) from by
          exact_mod_cast hi]
    linarith
  set t := ⌈ε * K⁻¹ ^ 2 * (B.card : ℝ)⌉₊
  have hS_paths : ∀ a₁ ∈ S, BSG.pathCount₂ B X a a₁ ≥ t :=
    fun a₁ ha₁ => Nat.ceil_le.mpr (hS_not_bad a₁ ha₁)
  have h_pc3 := BSG.pathCount₃_ge_of_many_good A B X a b S t hS_sub_A hS_conn_b hS_paths
  have h_pc3_real : (BSG.pathCount₃ A B X a b : ℝ) ≥ (S.card : ℝ) * (t : ℝ) := by
    exact_mod_cast h_pc3
  have ht_ge : (t : ℝ) ≥ ε * K⁻¹ ^ 2 * B.card := Nat.le_ceil _
  have hKinv_pos : (0 : ℝ) < K⁻¹ := inv_pos.mpr (by linarith)
  have hS_nn : (S.card : ℝ) ≥ 0 := Nat.cast_nonneg _
  have hεKB : ε * K⁻¹ ^ 2 * (B.card : ℝ) ≥ 0 := by positivity
  have step1 : (BSG.pathCount₃ A B X a b : ℝ) ≥ (S.card : ℝ) * (ε * K⁻¹ ^ 2 * B.card) :=
    calc (BSG.pathCount₃ A B X a b : ℝ) ≥ (S.card : ℝ) * (t : ℝ) := h_pc3_real
      _ ≥ (S.card : ℝ) * (ε * K⁻¹ ^ 2 * B.card) := mul_le_mul_of_nonneg_left ht_ge hS_nn
  have step2 : (S.card : ℝ) * (ε * K⁻¹ ^ 2 * B.card) ≥
    (10 * ε * (1/4 * K⁻¹ * (A.card : ℝ))) * (ε * K⁻¹ ^ 2 * B.card) := by
    have hS_ge : (S.card : ℝ) ≥ 10 * ε * (1/4 * K⁻¹ * A.card) := by
      nlinarith [hA'_card, hS_card]
    nlinarith [mul_le_mul_of_nonneg_right hS_ge hεKB]
  have step3 : (10 * ε * (1/4 * K⁻¹ * (A.card : ℝ))) * (ε * K⁻¹ ^ 2 * B.card) =
    10/4 * ε ^ 2 * K⁻¹ ^ 3 * A.card * B.card := by ring
  have step4 : 10/4 * ε ^ 2 * K⁻¹ ^ 3 * (A.card : ℝ) * B.card ≥
    10/4 * ε ^ 2 * K⁻¹ ^ 2 * (1/4) * K⁻¹ * A.card * B.card := by
    have h : 10/4 * ε ^ 2 * K⁻¹ ^ 3 * (A.card : ℝ) * B.card -
      10/4 * ε ^ 2 * K⁻¹ ^ 2 * (1/4) * K⁻¹ * A.card * B.card =
      (3/4) * (10/4) * ε ^ 2 * K⁻¹ ^ 3 * A.card * B.card := by ring
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (show (3:ℝ)/4 * (10/4) ≥ 0 from by norm_num)
      (sq_nonneg ε)) (by positivity : K⁻¹ ^ 3 ≥ 0))
      (Nat.cast_nonneg' A.card)) (Nat.cast_nonneg' B.card)]
  linarith
namespace BSG
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
/-- **Lemma (Key Lemma) for Balog–Szemerédi–Gowers.** If `X ⊆ A × B` has density
`|X| ≥ K⁻¹ |A| |B|`, then there exist refinements `A' ⊆ A`, `B' ⊆ B` and an exponent
`c ∈ ℕ` such that the restriction of `X` to `A' × B'` still has density `≥ K^{-c} |A||B|`
and every pair `(a, b) ∈ A' × B'` is joined by at least `K^{-c} |A||B|` length-3 paths in
the bipartite graph defined by `X`. -/
end BSG

/--
[pathCount](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/KeyLemmaBSG.lean)
-/
@[path]
private lemma pathCount_eq
  [DecidableEq α]
  [DecidableEq β]
  {A : Finset α}
  {B : Finset β}
  {X : Finset (α × β)}
  {a : α}
  {b : β}
  {S : Finset α}
  {t : ℕ}
-- given
  (hS_sub_A : S ⊆ A)
  (hS_conn_b : ∀ a₁ ∈ S, (a₁, b) ∈ X)
  (hS_paths : ∀ a₁ ∈ S, pathCount₂ B X a a₁ ≥ t) :
-- imply
  pathCount₃ A B X a b ≥ S.card * t := by
-- proof
  apply BSG.pathCount A B X a b S t hS_sub_A hS_conn_b hS_paths

/--
[pathCount](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/KeyLemmaBSG.lean)
-/
@[path]
private lemma pathCount_eq_2
  [DecidableEq α]
  [DecidableEq β]
  {A : Finset α}
  {B : Finset β}
  {a : α}
  {b : β}
-- given
  (ha : a ∈ A)
  (hb : b ∈ B) :
-- imply
  pathCount₃ A B (A ×ˢ B) a b = B.card * A.card := by
-- proof
  apply BSG.pathCount A B a b ha hb


-- created on 2026-10-23
