import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.ZPlusModules
open ZPlusModule


/--
[ZPlusRing.squaredCoeff_le_maxSquaredCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma ZPlusRing.squaredCoeff_le_maxSquaredCoeff
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [Nonempty ι]
  {k : ι} :
-- imply
  R.squaredCoeff k ≤ R.maxSquaredCoeff :=
-- proof
  Finset.le_sup' R.squaredCoeff (Finset.mem_univ k)

namespace ZPlusModule

/--
[act_unit_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma act_unit_self
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
  {l : κ} :
-- imply
  ∑ s ∈ R.I₀, M.act s l l = 1 := by
-- proof
  have h := M.act_unit l l; rw [if_pos rfl] at h; exact h

end ZPlusModule

namespace ZPlusModule

/--
[actCoeffSum_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma actCoeffSum_unit
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
  {l : κ} :
-- imply
  ∑ s ∈ R.I₀, M.actCoeffSum s l = 1 := by
-- proof
  simp only [actCoeffSum]
  rw [Finset.sum_comm]
  simp_rw [M.act_unit]
  simp

end ZPlusModule

namespace ZPlusModule

/--
[totalActCoeff_le_of_min](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma totalActCoeff_le_of_min
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
  [Nonempty ι]
  {l₀ : κ}
-- given
  (hmin : ∀ n : κ, M.totalActCoeff l₀ ≤ M.totalActCoeff n) :
-- imply
  M.totalActCoeff l₀ ≤ R.maxSquaredCoeff := by
-- proof
  by_cases hd : M.totalActCoeff l₀ = 0
  · omega
  have hpos : 0 < M.totalActCoeff l₀ := Nat.pos_of_ne_zero hd
  suffices h : M.totalActCoeff l₀ * M.totalActCoeff l₀ ≤
    R.maxSquaredCoeff * M.totalActCoeff l₀ from
    Nat.le_of_mul_le_mul_right h hpos
  have step1 : M.totalActCoeff l₀ * M.totalActCoeff l₀ ≤
    ∑ j : ι, ∑ n : κ, M.act j l₀ n * M.totalActCoeff n := by
    rw [show M.totalActCoeff l₀ = ∑ j : ι, ∑ n : κ, M.act j l₀ n from by
      simp only [totalActCoeff, actCoeffSum]]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro n _
    exact Nat.mul_le_mul_left _ (hmin n)
  have step2 : ∑ j : ι, ∑ n : κ, M.act j l₀ n * M.totalActCoeff n ≤
    R.maxSquaredCoeff * M.totalActCoeff l₀ := by
    calc ∑ j : ι, ∑ n : κ, M.act j l₀ n * M.totalActCoeff n
      = ∑ j : ι, ∑ n : κ, M.act j l₀ n * (∑ i : ι, M.actCoeffSum i n) := by rfl
      _ = ∑ j : ι, ∑ n : κ, ∑ i : ι, M.act j l₀ n * M.actCoeffSum i n := by
        congr 1; ext j; congr 1; ext n; rw [Finset.mul_sum]
      _ = ∑ j : ι, ∑ i : ι, ∑ n : κ, M.act j l₀ n * M.actCoeffSum i n := by
        congr 1; ext j; rw [Finset.sum_comm]
      _ = ∑ j : ι, ∑ i : ι, ∑ n : κ, M.act j l₀ n * ∑ k : κ, M.act i n k := by rfl
      _ = ∑ j : ι, ∑ i : ι, ∑ n : κ, ∑ k : κ, M.act j l₀ n * M.act i n k := by
        congr 1; ext j; congr 1; ext i; congr 1; ext n; rw [Finset.mul_sum]
      _ = ∑ j : ι, ∑ i : ι, ∑ k : κ, ∑ n : κ, M.act j l₀ n * M.act i n k := by
        congr 1; ext j; congr 1; ext i; rw [Finset.sum_comm]
      _ = ∑ j : ι, ∑ i : ι, ∑ k : κ, ∑ m : ι, R.N i j m * M.act m l₀ k := by
        congr 1; ext j; congr 1; ext i; congr 1; ext k
        exact (M.act_compat i j l₀ k).symm
      _ = ∑ i : ι, ∑ j : ι, ∑ k : κ, ∑ m : ι, R.N i j m * M.act m l₀ k := by
        rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ j : ι, ∑ m : ι, ∑ k : κ, R.N i j m * M.act m l₀ k := by
        congr 1; ext i; congr 1; ext j; rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ j : ι, ∑ m : ι, R.N i j m * M.actCoeffSum m l₀ := by
        congr 1; ext i; congr 1; ext j; congr 1; ext m
        simp only [actCoeffSum, Finset.mul_sum]
      _ = ∑ m : ι, R.squaredCoeff m * M.actCoeffSum m l₀ := by
        conv_lhs =>
          arg 2; ext i
          rw [Finset.sum_comm (f := fun j m => R.N i j m * M.actCoeffSum m l₀)]
        rw [Finset.sum_comm
          (f := fun i m => ∑ j, R.N i j m * M.actCoeffSum m l₀)]
        congr 1; ext m
        simp_rw [← Finset.sum_mul]
        rfl
      _ ≤ ∑ m : ι, R.maxSquaredCoeff * M.actCoeffSum m l₀ := by
        apply Finset.sum_le_sum; intro m _
        exact Nat.mul_le_mul_right _ (R.squaredCoeff_le_maxSquaredCoeff m)
      _ = R.maxSquaredCoeff * M.totalActCoeff l₀ := by
        rw [← Finset.mul_sum]; rfl
  exact le_trans step1 step2

end ZPlusModule

namespace ZPlusModule

/--
[act_pos_of_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma act_pos_of_irreducible
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
  {l k : κ}
-- given
  (hirr : M.IsIrreducible) :
-- imply
  ∃ i : ι, 0 < M.act i l k := by
-- proof
  classical
  let S := Finset.univ.filter (fun k' => ∃ i : ι, 0 < M.act i l k')
  have hl_in_S : l ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ l, ?_⟩
    have h1 := M.act_unit_self l
    by_contra hc
    simp only [not_exists, Nat.not_lt, Nat.le_zero] at hc
    have : ∑ s ∈ R.I₀, M.act s l l = 0 :=
      Finset.sum_eq_zero (fun s _ => hc s)
    omega
  have hS_closed : ∀ (j : ι) (k' : κ), k' ∈ S → ∀ (k'' : κ),
    M.act j k' k'' ≠ 0 → k'' ∈ S := by
    intro j k' hk' k'' hact
    have hk'_mem := (Finset.mem_filter.mp hk').2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ k'', ?_⟩
    obtain ⟨i₀, hi₀⟩ := hk'_mem
    have hcompat := M.act_compat j i₀ l k''
    have hact_pos : 0 < M.act j k' k'' := Nat.pos_of_ne_zero hact
    have hrhs_pos : 0 < ∑ n : κ, M.act i₀ l n * M.act j n k'' :=
      calc 0 < M.act i₀ l k' * M.act j k' k'' := Nat.mul_pos hi₀ hact_pos
        _ ≤ ∑ n : κ, M.act i₀ l n * M.act j n k'' :=
          Finset.single_le_sum (f := fun n => M.act i₀ l n * M.act j n k'')
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k')
    rw [← hcompat] at hrhs_pos
    by_contra hc2
    simp only [not_exists, Nat.not_lt, Nat.le_zero] at hc2
    have : ∑ m : ι, R.N j i₀ m * M.act m l k'' = 0 :=
      Finset.sum_eq_zero (fun m _ => by simp [hc2 m])
    omega
  by_cases hS_all : S = Finset.univ
  · have hk_in : k ∈ S := hS_all ▸ Finset.mem_univ k
    exact (Finset.mem_filter.mp hk_in).2
  · exfalso
    exact hirr S ⟨⟨l, hl_in_S⟩, hS_all, hS_closed⟩

end ZPlusModule

namespace ZPlusModule

/--
[card_le_totalActCoeff_of_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma card_le_totalActCoeff_of_irreducible
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
  {l : κ}
-- given
  (hirr : M.IsIrreducible) :
-- imply
  Fintype.card κ ≤ M.totalActCoeff l := by
-- proof
  unfold totalActCoeff actCoeffSum
  rw [Finset.sum_comm]
  calc Fintype.card κ = Finset.univ.card := Finset.card_univ.symm
    _ = ∑ _k ∈ (Finset.univ : Finset κ), 1 := by simp
    _ ≤ ∑ k ∈ (Finset.univ : Finset κ), ∑ i : ι, M.act i l k := by
      apply Finset.sum_le_sum
      intro k _
      obtain ⟨i₀, hi₀⟩ := M.act_pos_of_irreducible hirr l k
      calc 1 ≤ M.act i₀ l k := hi₀
        _ ≤ ∑ i : ι, M.act i l k :=
          Finset.single_le_sum (f := fun i => M.act i l k)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
    _ = ∑ k : κ, ∑ i : ι, M.act i l k := by rfl

end ZPlusModule

namespace ZPlusModule

/--
[prop_2_8_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma prop_2_8_7
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
  [Nonempty ι]
  [hκ : Nonempty κ]
-- given
  (hirr : M.IsIrreducible) :
-- imply
  Fintype.card κ ≤ R.maxSquaredCoeff := by
-- proof
  obtain ⟨l₀, _, hl₀⟩ := Finset.exists_min_image Finset.univ M.totalActCoeff
    ⟨Classical.arbitrary κ, Finset.mem_univ _⟩
  calc Fintype.card κ
    ≤ M.totalActCoeff l₀ := M.card_le_totalActCoeff_of_irreducible hirr l₀
    _ ≤ R.maxSquaredCoeff :=
      M.totalActCoeff_le_of_min l₀ (fun n => hl₀ n (Finset.mem_univ n))

end ZPlusModule

namespace ZPlusModule

/--
[IsIrreducible.isIndecomposable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma IsIrreducible.isIndecomposable
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
-- given
  (hirr : M.IsIrreducible) :
-- imply
  M.IsIndecomposable := by
-- proof
  intro S₁ S₂ hne₁ hne₂ hdisj _ hcl₁ _
  have hS₁_proper : S₁ ≠ Finset.univ := by
    intro heq
    have : S₂ = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      exact Finset.disjoint_right.mp hdisj hx (heq ▸ Finset.mem_univ x)
    exact hne₂.ne_empty this
  exact hirr S₁ ⟨hne₁, hS₁_proper, hcl₁⟩

end ZPlusModule

namespace ZPlusModule

/--
[lemma_2_8_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma lemma_2_8_5
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
-- given
  (hindec : M.IsIndecomposable)
  (hexact : M.IsExact) :
-- imply
  M.IsIrreducible := by
-- proof
  intro S hS
  have hSc_ne : (Finset.univ \ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hS.proper
    have : S = Finset.univ \ (Finset.univ \ S) := by simp
    rw [this, h]; simp
  have hdisj : Disjoint S (Finset.univ \ S) := disjoint_sdiff_self_right
  have hunion : S ∪ (Finset.univ \ S) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ S)
  have hSc_closed : ∀ (i : ι) (l : κ), l ∈ Finset.univ \ S → ∀ (k : κ),
    M.act i l k ≠ 0 → k ∈ Finset.univ \ S := by
    intro i l hl k hact
    rw [Finset.mem_sdiff] at hl ⊢
    exact ⟨Finset.mem_univ k, fun hk_in_S => by
      obtain ⟨j, hj⟩ := hexact i l k hact
      exact hl.2 (hS.closed j k hk_in_S l hj)⟩
  exact hindec S (Finset.univ \ S) hS.nonempty hSc_ne hdisj hunion hS.closed hSc_closed

end ZPlusModule

namespace ZPlusModule

/--
[decompose_finset_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma decompose_finset_aux
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ} :
-- imply
  ∀ S : Finset κ, S.Nonempty → M.IsActionClosed S → ∃ parts : Finset (Finset κ), (∀ k : κ, k ∈ S ↔ ∃ P ∈ parts, k ∈ P) ∧ (∀ P₁ ∈ parts, ∀ P₂ ∈ parts, P₁ ≠ P₂ → Disjoint P₁ P₂) ∧ (∀ P ∈ parts, P.Nonempty) ∧ (∀ P ∈ parts, M.IsActionClosed P) ∧ (∀ P ∈ parts, M.IsIndecomposablePiece P) := by
-- proof
  classical
  apply Finset.strongInduction
  intro S ih hne hclosed
  by_cases hindec : M.IsIndecomposablePiece S
  · exact ⟨{S},
    fun k => ⟨fun hk => ⟨S, Finset.mem_singleton_self S, hk⟩,
      fun ⟨P, hP, hk⟩ => Finset.mem_singleton.mp hP ▸ hk⟩,
    fun P₁ hP₁ P₂ hP₂ hne => by
      simp only [Finset.mem_singleton] at hP₁ hP₂
      exact absurd (hP₁.trans hP₂.symm) hne,
    fun P hP => by rw [Finset.mem_singleton.mp hP]; exact hne,
    fun P hP => by rw [Finset.mem_singleton.mp hP]; exact hclosed,
    fun P hP => by rw [Finset.mem_singleton.mp hP]; exact hindec⟩
  · unfold IsIndecomposablePiece at hindec
    push_neg at hindec
    obtain ⟨S₁, S₂, hne₁, hne₂, hdisj_S, hunion, hcl₁, hcl₂, _⟩ := hindec
    have hss₁ : S₁ ⊂ S := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨fun x hx => hunion ▸ Finset.mem_union_left S₂ hx,
        fun heq => by
          obtain ⟨y, hy⟩ := hne₂
          exact Finset.disjoint_left.mp hdisj_S
            (heq ▸ hunion ▸ Finset.mem_union_right S₁ hy) hy⟩
    have hss₂ : S₂ ⊂ S := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨fun x hx => hunion ▸ Finset.mem_union_right S₁ hx,
        fun heq => by
          obtain ⟨y, hy⟩ := hne₁
          exact Finset.disjoint_right.mp hdisj_S
            (heq ▸ hunion ▸ Finset.mem_union_left S₂ hy) hy⟩
    obtain ⟨parts₁, hcov₁, hdisj₁, hne₁', hcl₁', hindec₁⟩ := ih S₁ hss₁ hne₁ hcl₁
    obtain ⟨parts₂, hcov₂, hdisj₂, hne₂', hcl₂', hindec₂⟩ := ih S₂ hss₂ hne₂ hcl₂
    have hp₁_sub : ∀ P ∈ parts₁, P ⊆ S₁ :=
      fun P hP k hk => (hcov₁ k).mpr ⟨P, hP, hk⟩
    have hp₂_sub : ∀ P ∈ parts₂, P ⊆ S₂ :=
      fun P hP k hk => (hcov₂ k).mpr ⟨P, hP, hk⟩
    refine ⟨parts₁ ∪ parts₂, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro k; constructor
      · intro hk
        rw [← hunion, Finset.mem_union] at hk
        cases hk with
        | inl hk₁ =>
          have ⟨P, hP, hkP⟩ := (hcov₁ k).mp hk₁
          exact ⟨P, Finset.mem_union_left _ hP, hkP⟩
        | inr hk₂ =>
          have ⟨P, hP, hkP⟩ := (hcov₂ k).mp hk₂
          exact ⟨P, Finset.mem_union_right _ hP, hkP⟩
      · intro ⟨P, hP, hkP⟩
        rw [Finset.mem_union] at hP; rw [← hunion]
        cases hP with
        | inl hP₁ => exact Finset.mem_union_left _ ((hcov₁ k).mpr ⟨P, hP₁, hkP⟩)
        | inr hP₂ => exact Finset.mem_union_right _ ((hcov₂ k).mpr ⟨P, hP₂, hkP⟩)
    ·
      intro P₁ hP₁ P₂ hP₂ hne_P
      rw [Finset.mem_union] at hP₁ hP₂
      match hP₁, hP₂ with
      | .inl h₁, .inl h₂ => exact hdisj₁ P₁ h₁ P₂ h₂ hne_P
      | .inr h₁, .inr h₂ => exact hdisj₂ P₁ h₁ P₂ h₂ hne_P
      | .inl h₁, .inr h₂ =>
        exact Finset.disjoint_of_subset_left (hp₁_sub P₁ h₁)
          (Finset.disjoint_of_subset_right (hp₂_sub P₂ h₂) hdisj_S)
      | .inr h₁, .inl h₂ =>
        exact Finset.disjoint_of_subset_left (hp₂_sub P₁ h₁)
          (Finset.disjoint_of_subset_right (hp₁_sub P₂ h₂) hdisj_S.symm)
    ·
      intro P hP; rw [Finset.mem_union] at hP
      cases hP with | inl h => exact hne₁' P h | inr h => exact hne₂' P h
    ·
      intro P hP; rw [Finset.mem_union] at hP
      cases hP with | inl h => exact hcl₁' P h | inr h => exact hcl₂' P h
    ·
      intro P hP; rw [Finset.mem_union] at hP
      cases hP with | inl h => exact hindec₁ P h | inr h => exact hindec₂ P h

end ZPlusModule

namespace ZPlusModule

/--
[exists_indecomposable_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma exists_indecomposable_decomposition
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
  [Nonempty κ] :
-- imply
  ∃ parts : Finset (Finset κ), M.IsZPlusDecomposition parts ∧ ∀ P ∈ parts, M.IsIndecomposablePiece P := by
-- proof
  have hne : (Finset.univ : Finset κ).Nonempty := Finset.univ_nonempty
  have hclosed : M.IsActionClosed Finset.univ :=
    fun _ _ _ _ _ => Finset.mem_univ _
  obtain ⟨parts, hcov, hdisj, hne', hcl', hindec⟩ :=
    M.decompose_finset_aux Finset.univ hne hclosed
  exact ⟨parts,
    ⟨fun k => (hcov k).mp (Finset.mem_univ k), hdisj, hne', hcl'⟩,
    hindec⟩

end ZPlusModule

namespace ZPlusModule

/--
[indecomposable_piece_irreducible_of_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma indecomposable_piece_irreducible_of_exact
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
  {S : Finset κ}
-- given
  (hexact : M.IsExact)
  (hclosed : M.IsActionClosed S)
  (hindec : M.IsIndecomposablePiece S) :
-- imply
  M.IsIrreduciblePiece S := by
-- proof
  intro T hTne hTne_S hTsub hTclosed
  have hunion : T ∪ (S \ T) = S := Finset.union_sdiff_of_subset hTsub
  have hSdiff_ne : (S \ T).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hTne_S
    exact Finset.Subset.antisymm hTsub (by
      intro x hx; by_contra hxT
      exact Finset.notMem_empty x (h ▸ Finset.mem_sdiff.mpr ⟨hx, hxT⟩))
  have hSdiff_closed : M.IsActionClosed (S \ T) := by
    intro i l hl k hact
    rw [Finset.mem_sdiff] at hl ⊢
    exact ⟨hclosed i l hl.1 k hact, fun hkT => by
      obtain ⟨j, hj⟩ := hexact i l k hact
      exact hl.2 (hTclosed j k hkT l hj)⟩
  exact hindec T (S \ T) hTne hSdiff_ne Finset.disjoint_sdiff hunion hTclosed hSdiff_closed

end ZPlusModule

/--
[Proposition_2_8_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean)
-/
@[path]
lemma Proposition_2_8_7
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  [DecidableEq ι]
  [Fintype ι]
  [Nonempty ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  [Nonempty κ]
  {M : ZPlusModule R κ}
-- given
  (hirr : M.IsIrreducible) :
-- imply
  Fintype.card κ ≤ R.maxSquaredCoeff :=
-- proof
  M.prop_2_8_7 hirr


-- created on 2026-10-23
