import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words.lean)
-/
@[path]
private lemma main
  [AddCommGroup V]
  {σ i j : V →+ V}
  {m : V →+ V}
-- given
  (hσ3 : ∀ T, σ (σ (σ T)) = T)
  (hi : ∀ T, i (i T) = -T)
  (hj : ∀ T, j (j T) = -T)
  (hij : ∀ T, i (j T) = -(j (i T)))
  (hσi : ∀ T, σ (i T) = j (σ T))
  (hσj : ∀ T, σ (j T) = j (i (σ T)))
  (hσ : ∀ T, σ (σ T) + σ T + T = 0)
  (hm : m = AddMonoidHom.id _ ∨ m = σ ∨ m = σ.comp σ ∨ m = i ∨ m = i.comp σ ∨ m = i.comp (σ.comp σ) ∨ m = j ∨ m = j.comp σ ∨ m = j.comp (σ.comp σ) ∨ m = i.comp j ∨ m = (i.comp j).comp σ ∨ m = (i.comp j).comp (σ.comp σ)) :
-- imply
  ∃ t : ℤ, (t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧ (t = 2 → m = AddMonoidHom.id _) ∧
      ∀ T, m (m T) - t • m T + T = 0 := by
-- proof
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    refine ⟨2, by norm_num, fun _ => rfl, fun T => ?_⟩
    simp only [AddMonoidHom.id_apply]
    abel
  ·
    refine ⟨-1, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    have E0 := congrArg (fun w => w) (hσ (T))
    simp only [neg_smul, one_smul, sub_neg_eq_add] at E0 ⊢
    linear_combination (norm := abel) E0
  ·
    refine ⟨-1, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    have E0 := congrArg (fun w => w) (hσ (T))
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, hσ3, neg_smul, one_smul, sub_neg_eq_add] at E0 ⊢
    linear_combination (norm := abel) E0
  ·
    refine ⟨0, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    simp only [hi, zero_smul, sub_zero]
    abel
  ·
    refine ⟨-1, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    have E0 := congrArg (fun w => j (w)) (hσ (i (σ (σ (T)))))
    simp only [map_add, map_zero, AddMonoidHom.coe_comp, Function.comp_apply, hσ3, hj, hij, hσi, hσj, neg_smul, one_smul, sub_neg_eq_add] at E0 ⊢
    have E0' := neg_eq_zero.mpr E0
    simp only [neg_add_rev, neg_neg] at E0'
    linear_combination (norm := abel) E0'
  ·
    refine ⟨1, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    have E0 := congrArg (fun w => j (i (w))) (hσ (i (σ (T))))
    simp only [map_add, map_zero, map_neg, AddMonoidHom.coe_comp, Function.comp_apply, hσ3, hi, hj, hij, hσi, hσj, neg_neg, one_smul] at E0 ⊢
    have E0' := neg_eq_zero.mpr E0
    simp only [neg_add_rev, neg_neg] at E0'
    linear_combination (norm := abel) E0'
  ·
    refine ⟨0, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    simp only [hj, zero_smul, sub_zero]
    abel
  ·
    refine ⟨-1, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    have E0 := congrArg (fun w => j (i (w))) (hσ (i (σ (T))))
    simp only [map_add, map_zero, map_neg, AddMonoidHom.coe_comp, Function.comp_apply, hσ3, hi, hj, hij, hσi, hσj, neg_neg, neg_smul, one_smul, sub_neg_eq_add] at E0 ⊢
    have E0' := neg_eq_zero.mpr E0
    simp only [neg_add_rev, neg_neg] at E0'
    linear_combination (norm := abel) E0'
  ·
    refine ⟨1, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    have E0 := congrArg (fun w => i (w)) (hσ (i (T)))
    simp only [map_add, map_zero, map_neg, AddMonoidHom.coe_comp, Function.comp_apply, hσ3, hi, hj, hij, hσi, hσj, neg_neg, one_smul] at E0 ⊢
    have E0' := neg_eq_zero.mpr E0
    simp only [neg_add_rev, neg_neg] at E0'
    linear_combination (norm := abel) E0'
  ·
    refine ⟨0, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    simp only [map_neg, AddMonoidHom.coe_comp, Function.comp_apply, hi, hj, hij, neg_neg, zero_smul, sub_zero]
    abel
  ·
    refine ⟨1, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    have E0 := congrArg (fun w => i (w)) (hσ (i (T)))
    simp only [map_add, map_zero, map_neg, AddMonoidHom.coe_comp, Function.comp_apply, hi, hj, hij, hσi, hσj, neg_neg, one_smul, sub_neg_eq_add] at E0 ⊢
    have E0' := neg_eq_zero.mpr E0
    simp only [neg_add_rev, neg_neg] at E0'
    linear_combination (norm := abel) E0'
  ·
    refine ⟨-1, by norm_num, fun h => absurd h (by norm_num), fun T => ?_⟩
    have E0 := congrArg (fun w => j (w)) (hσ (i (σ (σ (T)))))
    simp only [map_add, map_zero, map_neg, AddMonoidHom.coe_comp, Function.comp_apply, hσ3, hj, hij, hσi, hσj, neg_neg, neg_smul, one_smul] at E0 ⊢
    have E0' := neg_eq_zero.mpr E0
    simp only [neg_add_rev, neg_neg] at E0'
    linear_combination (norm := abel) E0'


-- created on 2026-10-09
