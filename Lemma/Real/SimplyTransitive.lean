import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.ReflectionGroupsCoxeter
open Set HyperplaneArrangement
open scoped InnerProductSpace


namespace HyperplaneArrangement

/--
[simplyTransitive_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma simplyTransitive_theorem
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr] :
-- imply
  arr.SimplyTransitive := by
-- proof
  intro C D
  obtain ⟨w, hw⟩ := CoxeterArrangement.transitive_on_chambers (arr := arr) C D
  refine ⟨w, hw, ?_⟩
  intro w' hw'
  have h_fix : w'⁻¹ * w = ⟨1, one_mem _⟩ := by
    apply CoxeterArrangement.faithful_on_chambers C
    show imageByIsometry (↑(w'⁻¹ * w)) C.set = C.set
    ext x; simp only [imageByIsometry, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hwy : (↑w : AffineIsometryEquiv ℝ E E) y ∈ D.set := by rw [← hw]; exact ⟨y, hy, rfl⟩
      have : (↑w' : AffineIsometryEquiv ℝ E E).symm ((↑w : AffineIsometryEquiv ℝ E E) y) ∈ C.set := by
        rw [← hw'] at hwy; obtain ⟨z, hz, hze⟩ := hwy
        rw [show (↑w' : AffineIsometryEquiv ℝ E E).symm ((↑w : AffineIsometryEquiv ℝ E E) y) =
          (↑w' : AffineIsometryEquiv ℝ E E).symm ((↑w' : AffineIsometryEquiv ℝ E E) z) from by rw [hze]]
        simp [AffineIsometryEquiv.symm_apply_apply]; exact hz
      convert this using 1
    · intro hx
      refine ⟨(↑w : AffineIsometryEquiv ℝ E E).symm ((↑w' : AffineIsometryEquiv ℝ E E) x), ?_, ?_⟩
      · have hw'x : (↑w' : AffineIsometryEquiv ℝ E E) x ∈ D.set := by rw [← hw']; exact ⟨x, hx, rfl⟩
        rw [← hw] at hw'x; obtain ⟨z, hz, hze⟩ := hw'x
        rw [show (↑w : AffineIsometryEquiv ℝ E E).symm ((↑w' : AffineIsometryEquiv ℝ E E) x) =
          (↑w : AffineIsometryEquiv ℝ E E).symm ((↑w : AffineIsometryEquiv ℝ E E) z) from by rw [hze]]
        simp [AffineIsometryEquiv.symm_apply_apply]; exact hz
      · show (↑(w'⁻¹ * w) : AffineIsometryEquiv ℝ E E) ((↑w : AffineIsometryEquiv ℝ E E).symm ((↑w' : AffineIsometryEquiv ℝ E E) x)) = x
        simp [Subgroup.coe_mul]
  have : w = w' := by
    have h1 := congr_arg Subtype.val h_fix
    simp [Subgroup.coe_mul] at h1
    ext1
    calc (w : AffineIsometryEquiv ℝ E E) = (↑w' * (↑w')⁻¹) * ↑w := by simp
      _ = ↑w' * ((↑w')⁻¹ * ↑w) := by rw [mul_assoc]
      _ = ↑w' * 1 := by rw [h1]
      _ = ↑w' := by rw [mul_one]
  exact this.symm

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[fundamentalDomain_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma fundamentalDomain_theorem
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr]
  {C : arr.Chamber} :
-- imply
  arr.FundamentalDomain C := by
-- proof
  constructor
  · intro x; exact CoxeterArrangement.closure_covers C x
  · intro w₁ w₂ hw; exact CoxeterArrangement.open_chambers_disjoint C w₁ w₂ hw

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[wallReflection_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma wallReflection_involutive
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr]
  {C : arr.Chamber}
  {s : AffineIsometryEquiv ℝ E E}
-- given
  (hs : s ∈ arr.wallReflections C) :
-- imply
  s * s = 1 := by
-- proof
  obtain ⟨η, hη_wall, hs_eq⟩ := hs
  subst hs_eq
  exact CoxeterArrangement.reflection_involutive η hη_wall.1

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[deletionCondition_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma deletionCondition_theorem
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr]
  {C : arr.Chamber} :
-- imply
  arr.DeletionCondition C := by
-- proof
  intro word hword hlen
  induction word using List.rec with
  | nil => simp at hlen
  | cons s rest ih =>
    by_cases hrest : arr.wordLength C rest.prod < rest.length
    · have hrest_word : ∀ t ∈ rest, t ∈ arr.wallReflections C :=
      fun t ht => hword t (List.mem_cons_of_mem s ht)
      obtain ⟨i, j, hij, hprod⟩ := ih hrest_word hrest
      refine ⟨⟨i.val + 1, by simp⟩, ⟨j.val + 1, by simp⟩, by simp; omega, ?_⟩
      simp only [List.eraseIdx_cons_succ, List.prod_cons]
      rw [hprod]
    · push Not at hrest
      have hs : s ∈ arr.wallReflections C := hword s (List.mem_cons.mpr (Or.inl rfl))
      have hrest_word : ∀ t ∈ rest, t ∈ arr.wallReflections C :=
        fun t ht => hword t (List.mem_cons_of_mem s ht)
      have hle : arr.wordLength C rest.prod ≤ rest.length := by
        apply Nat.sInf_le; exact ⟨rest, ⟨hrest_word, rfl⟩, rfl⟩
      have hrest_eq : arr.wordLength C rest.prod = rest.length := le_antisymm hle hrest
      have hle2 : arr.wordLength C (s * rest.prod) ≤ arr.wordLength C rest.prod := by
        rw [hrest_eq]
        simp only [List.prod_cons] at hlen
        simp only [List.length_cons] at hlen
        omega
      have hIsWord : arr.IsWordFor C rest rest.prod := ⟨hrest_word, rfl⟩
      obtain ⟨i, hi⟩ := CoxeterArrangement.exchange_property C s hs rest hrest_word hIsWord hle2
      refine ⟨⟨0, by simp⟩, ⟨i.val + 1, by simp⟩, by simp, ?_⟩
      simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, List.prod_cons]
      exact hi.symm

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[wallReflections_generate_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma wallReflections_generate_theorem
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr]
  {C : arr.Chamber} :
-- imply
  arr.WallReflectionGroup C = arr.ReflectionGroup := by
-- proof
  apply le_antisymm
  ·
    apply (Subgroup.closure_le _).mpr
    intro g hg
    obtain ⟨η, hη_wall, hg_eq⟩ := hg
    apply Subgroup.subset_closure
    exact ⟨η, hη_wall.1, hg_eq⟩
  ·
    apply (Subgroup.closure_le _).mpr
    intro g hg
    obtain ⟨η, hη, hg_eq⟩ := hg
    subst hg_eq
    obtain ⟨D, hD⟩ := CoxeterArrangement.reflection_maps_chambers η hη C
    obtain ⟨w, hw_mem, hw_eq⟩ := CoxeterArrangement.transitive_via_wall_reflections C D
    have hD_eq : imageByIsometry w C.set = D.set := hw_eq
    obtain ⟨s, hs, hconj⟩ := CoxeterArrangement.wall_reflection_conjugate C w hw_mem D hD_eq
      η.reflectionMap
      ⟨η, ⟨hη, CoxeterArrangement.reflection_creates_wall η hη C D hD⟩, rfl⟩
    rw [hconj]
    have hs_mem : s ∈ arr.WallReflectionGroup C := Subgroup.subset_closure hs
    exact (arr.WallReflectionGroup C).mul_mem
      ((arr.WallReflectionGroup C).mul_mem hw_mem hs_mem)
      (inv_mem hw_mem)

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[reverse_prod_of_involutions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma reverse_prod_of_involutions
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr]
  [Group G]
  {wa : List G}
-- given
  (hinv : ∀ s ∈ wa, s * s = 1) :
-- imply
  wa.reverse.prod = wa.prod⁻¹ := by
-- proof
  rw [List.prod_reverse_noncomm]
  congr 1
  have hmap : List.map (fun x => x⁻¹) wa = wa := by
    induction wa with
    | nil => simp
    | cons a' rest ih_rest =>
      simp only [List.map_cons]
      congr 1
      · have ha := hinv a' (List.mem_cons.mpr (Or.inl rfl))
        exact mul_left_cancel (a := a') (by rw [ha, mul_inv_cancel])
      · exact ih_rest (fun s hs => hinv s (List.mem_cons.mpr (Or.inr hs)))
  rw [hmap]

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[word_exists_for_closure_element](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma word_exists_for_closure_element
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr]
  {C : arr.Chamber}
  {w : AffineIsometryEquiv ℝ E E}
-- given
  (hw : w ∈ arr.WallReflectionGroup C) :
-- imply
  ∃ word : List (AffineIsometryEquiv ℝ E E), (∀ s ∈ word, s ∈ arr.wallReflections C) ∧ word.prod = w := by
-- proof
  have hinv : ∀ s ∈ arr.wallReflections C, s * s = 1 :=
    fun s hs => wallReflection_involutive C s hs
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ word : List (AffineIsometryEquiv ℝ E E),
      (∀ s ∈ word, s ∈ arr.wallReflections C) ∧ word.prod = g) ?_ ?_ ?_ ?_ hw
  · intro x hx'; exact ⟨[x], fun s hs => by simp at hs; rwa [hs], by simp⟩
  · exact ⟨[], fun s hs => by simp at hs, by simp⟩
  · intro a b _ _ ⟨wa, hwa_mem, hwa_prod⟩ ⟨wb, hwb_mem, hwb_prod⟩
    exact ⟨wa ++ wb, fun s hs => by
      rw [List.mem_append] at hs
      exact hs.elim (hwa_mem s) (hwb_mem s),
      by rw [List.prod_append, hwa_prod, hwb_prod]⟩
  · intro a _ ⟨wa, hwa_mem, hwa_prod⟩
    refine ⟨wa.reverse, fun s hs => hwa_mem s (List.mem_reverse.mp hs), ?_⟩
    rw [← hwa_prod]
    exact reverse_prod_of_involutions wa (fun s hs => hinv s (hwa_mem s hs))

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[lengthEqualsGalleryDistance_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma lengthEqualsGalleryDistance_theorem
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr]
  {C : arr.Chamber} :
-- imply
  arr.LengthEqualsGalleryDistance C := by
-- proof
  intro w hw x hx
  apply le_antisymm
  ·
    exact CoxeterArrangement.gallery_lower_bound C w hw x hx
  ·
    apply le_csInf
    ·
      have hw_mem : w ∈ arr.WallReflectionGroup C := by
        rw [wallReflections_generate_theorem C]; exact hw
      obtain ⟨word, hword_mem, hword_prod⟩ := word_exists_for_closure_element C w hw_mem
      exact ⟨word.length, word, ⟨hword_mem, hword_prod⟩, rfl⟩
    · intro n ⟨word, ⟨hword_mem, hword_prod⟩, hword_len⟩
      rw [← hword_len, ← hword_prod]
      exact CoxeterArrangement.gallery_upper_bound C word hword_mem x hx

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[isotropyGeneratedByReflections_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma isotropyGeneratedByReflections_theorem
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr]
  {C : arr.Chamber} :
-- imply
  arr.IsotropyGeneratedByReflections C := by
-- proof
  intro x hx
  apply le_antisymm
  ·
    intro w hw_iso
    have hw_mem : w ∈ arr.ReflectionGroup := hw_iso.1
    have hw_fix : w x = x := hw_iso.2
    have hw_wall : w ∈ arr.WallReflectionGroup C := by
      rw [wallReflections_generate_theorem C]; exact hw_mem
    suffices key : ∀ (n : ℕ) (g : AffineIsometryEquiv ℝ E E),
      g ∈ arr.WallReflectionGroup C →
      g x = x →
      arr.wordLength C g = n →
      g ∈ Subgroup.closure (arr.reflectionsThrough x) by
      exact key (arr.wordLength C w) w hw_wall hw_fix rfl
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro g hg_wall hg_fix hg_len
    by_cases hn : n = 0
    ·
      subst hn
      have hne : { n : ℕ | ∃ word : List (AffineIsometryEquiv ℝ E E),
        arr.IsWordFor C word g ∧ word.length = n }.Nonempty := by
        obtain ⟨word, hword_mem, hword_prod⟩ := word_exists_for_closure_element C g hg_wall
        exact ⟨word.length, word, ⟨hword_mem, hword_prod⟩, rfl⟩
      have h0 : arr.wordLength C g ∈ { n : ℕ | ∃ word : List (AffineIsometryEquiv ℝ E E),
        arr.IsWordFor C word g ∧ word.length = n } := Nat.sInf_mem hne
      rw [hg_len] at h0
      obtain ⟨word, ⟨_, hword_prod⟩, hword_len⟩ := h0
      have hnil : word = [] := List.eq_nil_of_length_eq_zero hword_len
      subst hnil
      simp at hword_prod
      rw [← hword_prod]
      exact one_mem _
    ·
      have hne : { k : ℕ | ∃ word : List (AffineIsometryEquiv ℝ E E),
        arr.IsWordFor C word g ∧ word.length = k }.Nonempty := by
        obtain ⟨word, hword_mem, hword_prod⟩ := word_exists_for_closure_element C g hg_wall
        exact ⟨word.length, word, ⟨hword_mem, hword_prod⟩, rfl⟩
      have h_in : arr.wordLength C g ∈ { k : ℕ | ∃ word : List (AffineIsometryEquiv ℝ E E),
        arr.IsWordFor C word g ∧ word.length = k } := Nat.sInf_mem hne
      rw [hg_len] at h_in
      obtain ⟨word, ⟨hword_wall, hword_prod⟩, hword_len⟩ := h_in
      obtain ⟨s₁, rest, rfl⟩ : ∃ s₁ rest, word = s₁ :: rest := by
        cases word with
        | nil => simp at hword_len; omega
        | cons h t => exact ⟨h, t, rfl⟩
      simp only [List.length_cons] at hword_len
      have hs₁ : s₁ ∈ arr.wallReflections C :=
        hword_wall s₁ (List.mem_cons.mpr (Or.inl rfl))
      have hrest_wall : ∀ t ∈ rest, t ∈ arr.wallReflections C :=
        fun t ht => hword_wall t (List.mem_cons.mpr (Or.inr ht))
      have hreduced : arr.wordLength C ((s₁ :: rest).prod) = (s₁ :: rest).length := by
        rw [hword_prod, hg_len]; simp [hword_len]
      have hg_eq : (s₁ :: rest).prod = g := hword_prod
      obtain ⟨η₁, hη₁_wall, hs₁_eq, hx_in⟩ :=
        CoxeterArrangement.closure_wall_membership C s₁ rest hs₁ hrest_wall
          hreduced x hx (by rw [hg_eq, hg_fix])
      have hs₁_fix : s₁ x = x := by
        rw [hs₁_eq]
        exact CoxeterArrangement.wall_reflection_fixes_wall_point η₁ hη₁_wall.1 x hx_in
      have hs₁_refl_through : s₁ ∈ arr.reflectionsThrough x :=
        ⟨η₁, ⟨hη₁_wall.1, hx_in⟩, hs₁_eq⟩
      have hs₁_in_closure : s₁ ∈ Subgroup.closure (arr.reflectionsThrough x) :=
        Subgroup.subset_closure hs₁_refl_through
      have hs₁g_eq : s₁ * g = rest.prod := by
        rw [← hg_eq]
        simp only [List.prod_cons]
        rw [← mul_assoc]
        have : s₁ * s₁ = 1 := wallReflection_involutive C s₁ hs₁
        rw [this, one_mul]
      have hs₁g_fix : (s₁ * g) x = x := by
        show s₁ (g x) = x
        rw [hg_fix, hs₁_fix]
      have hs₁g_wall : s₁ * g ∈ arr.WallReflectionGroup C :=
        (arr.WallReflectionGroup C).mul_mem (Subgroup.subset_closure hs₁) hg_wall
      have hs₁g_len : arr.wordLength C (s₁ * g) ≤ rest.length := by
        rw [hs₁g_eq]
        apply Nat.sInf_le
        exact ⟨rest, ⟨hrest_wall, rfl⟩, rfl⟩
      have hrest_len : rest.length = n - 1 := by omega
      have hs₁g_lt : arr.wordLength C (s₁ * g) < n := by omega
      have hs₁g_in : s₁ * g ∈ Subgroup.closure (arr.reflectionsThrough x) :=
        ih (arr.wordLength C (s₁ * g)) hs₁g_lt (s₁ * g) hs₁g_wall hs₁g_fix rfl
      have hg_decomp : g = s₁ * (s₁ * g) := by
        rw [← mul_assoc]
        have : s₁ * s₁ = 1 := wallReflection_involutive C s₁ hs₁
        rw [this, one_mul]
      rw [hg_decomp]
      exact (Subgroup.closure (arr.reflectionsThrough x)).mul_mem hs₁_in_closure hs₁g_in
  ·
    apply (Subgroup.closure_le _).mpr
    intro g hg
    obtain ⟨η, ⟨hη_hyp, hη_mem⟩, hg_eq⟩ := hg
    simp only [SetLike.mem_coe]
    constructor
    · rw [hg_eq]
      exact Subgroup.subset_closure ⟨η, hη_hyp, rfl⟩
    · rw [hg_eq]
      exact CoxeterArrangement.wall_reflection_fixes_wall_point η hη_hyp x hη_mem

end HyperplaneArrangement


-- created on 2026-10-23
-- updated on 2026-10-24
