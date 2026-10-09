import Mathlib
import sympy.Basic


/--
[AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_dicyclic_relations_of_char_three_words](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_dicyclic_relations_of_char_three_words.lean)
-/
@[path]
private lemma main
  [AddCommGroup V]
  {α β m : V →+ V}
-- given
  (hα : ∀ T, α (α T) = -T)
  (hβ : ∀ T, β (β T) + β T + T = 0)
  (hαβ : ∀ T, α (β T) = β (β (α T)))
  (hm : m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨ m = α.comp (β.comp β)) :
-- imply
  ∃ t : ℤ, (t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧ (t = 2 → m = AddMonoidHom.id _) ∧
      ∀ T, m (m T) - t • m T + T = 0 := by
-- proof
  have hβ3 : ∀ S, β (β (β S)) = S := by
    intro S
    have h1 := hβ (β S)
    have h2 := hβ S
    calc _ = (β (β (β S)) + β (β S) + β S) - (β (β S) + β S + S) + S := by abel
      _ = S := by rw [h1, h2]; abel

  have hββ : ∀ T, β (β (β (β T))) - (-1 : ℤ) • β (β T) + T = 0 := by
    intro T
    rw [hβ3, neg_one_zsmul, sub_neg_eq_add]
    have h2 := hβ T
    calc _ = β (β T) + β T + T := by abel
      _ = 0 := h2

  have hαβ2 : ∀ T, α (β (α (β T))) = -T := by
    intro T
    rw [hαβ (α (β T)), hα, map_neg, map_neg, hβ3]

  have hαββ : ∀ T, α (β (β T)) = β (α T) := by
    intro T
    rw [hαβ (β T), hαβ T, hβ3]

  have hβα2 : ∀ T, β (α (β (α T))) = -T := by
    intro T
    rw [hαβ (α T), hα, map_neg, map_neg, map_neg, hβ3]
  obtain rfl | rfl | rfl | rfl | rfl | rfl := hm
  · exact ⟨2, by norm_num, fun _ => rfl, fun T => by simp [two_zsmul]⟩
  · refine ⟨0, by norm_num, by norm_num, fun T => ?_⟩
    rw [zero_zsmul, sub_zero, hα, neg_add_cancel]
  · refine ⟨-1, by norm_num, by norm_num, fun T => ?_⟩
    rw [neg_one_zsmul, sub_neg_eq_add]; exact hβ T
  · refine ⟨-1, by norm_num, by norm_num, fun T => ?_⟩
    simpa only [AddMonoidHom.comp_apply] using hββ T
  ·
    refine ⟨0, by norm_num, by norm_num, fun T => ?_⟩
    simp only [AddMonoidHom.comp_apply, zero_zsmul, sub_zero]
    rw [hαβ2, neg_add_cancel]
  ·
    refine ⟨0, by norm_num, by norm_num, fun T => ?_⟩
    simp only [AddMonoidHom.comp_apply, zero_zsmul, sub_zero]
    rw [hαββ, hαββ, hβα2, neg_add_cancel]


-- created on 2026-10-09
