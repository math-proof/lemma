/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part8


namespace MetaMathlibExt

/-- Value formula for the two-block permutation. -/
lemma ntBeta_val {n j : ℕ} (hj : j + 1 ≤ n) (i : Fin n) :
    ((ntBeta n j hj) i).val =
      if i.val < j then j - 1 - i.val else n + j - 1 - i.val := by
  have e : (ntBeta n j hj) i = ntBetaFun n j hj i := rfl
  rw [e, ntBetaFun_val]

/-- An increasing value pair in `beta` forces low then high blocks. -/
lemma ntBeta_force {n j : ℕ} (hj : j + 1 ≤ n) {x y : Fin n}
    (hxy : x.val < y.val) (h : (ntBeta n j hj) x < (ntBeta n j hj) y) :
    x.val < j ∧ j ≤ y.val := by
  rw [Fin.lt_def, ntBeta_val hj, ntBeta_val hj] at h
  by_cases hx : x.val < j
  · by_cases hyj : y.val < j
    · rw [ite_eq_left hx, ite_eq_left hyj] at h
      omega
    · exact ⟨hx, not_lt.mp hyj⟩
  · by_cases hyj : y.val < j
    · omega
    · rw [ite_eq_right hx, ite_eq_right hyj] at h
      omega

/-- A decreasing value pair in `beta` forces high or low blocks. -/
lemma ntBeta_force_gt {n j : ℕ} (hj : j + 1 ≤ n) {x y : Fin n}
    (_hxy : x.val < y.val) (h : (ntBeta n j hj) y < (ntBeta n j hj) x) :
    j ≤ x.val ∨ y.val < j := by
  by_cases hx : x.val < j
  · by_cases hyj : y.val < j
    · exact Or.inr hyj
    · exfalso
      have hlt : (ntBeta n j hj) x < (ntBeta n j hj) y := by
        rw [Fin.lt_def, ntBeta_val hj, ntBeta_val hj, ite_eq_left hx, ite_eq_right hyj]
        have := y.is_lt
        omega
      exact absurd (lt_trans hlt h) (lt_irrefl _)
  · exact Or.inl (not_lt.mp hx)

/-- The two-block permutation has no increasing triple. -/
lemma ntBeta_no123 {n j : ℕ} (hj : j + 1 ≤ n) :
    ¬∃ a b c : Fin n, a.val < b.val ∧ b.val < c.val ∧
      (ntBeta n j hj) a < (ntBeta n j hj) b ∧
      (ntBeta n j hj) b < (ntBeta n j hj) c := by
  rintro ⟨a, b, c, hab, hbc, h1, h2⟩
  obtain ⟨ha, hbhi⟩ := ntBeta_force hj hab h1
  obtain ⟨hb, -⟩ := ntBeta_force hj hbc h2
  omega

/-- The two-block permutation has no 231 triple. -/
lemma ntBeta_no231 {n j : ℕ} (hj : j + 1 ≤ n) :
    ¬∃ a b c : Fin n, a.val < b.val ∧ b.val < c.val ∧
      (ntBeta n j hj) c < (ntBeta n j hj) a ∧
      (ntBeta n j hj) a < (ntBeta n j hj) b := by
  rintro ⟨a, b, c, hab, hbc, hca, habv⟩
  have hac : a.val < c.val := lt_trans hab hbc
  obtain ⟨ha, hbhi⟩ := ntBeta_force hj hab habv
  rcases ntBeta_force_gt hj hac hca with ha' | hc
  · omega
  · omega

/-- The two-block permutation has no 312 triple. -/
lemma ntBeta_no312 {n j : ℕ} (hj : j + 1 ≤ n) :
    ¬∃ a b c : Fin n, a.val < b.val ∧ b.val < c.val ∧
      (ntBeta n j hj) b < (ntBeta n j hj) c ∧
      (ntBeta n j hj) c < (ntBeta n j hj) a := by
  rintro ⟨a, b, c, hab, hbc, hbcv, hcav⟩
  have hac : a.val < c.val := lt_trans hab hbc
  obtain ⟨hb, hchi⟩ := ntBeta_force hj hbc hbcv
  rcases ntBeta_force_gt hj hac hcav with ha | hc
  · omega
  · omega

/-- A pattern in a swapped two-block permutation sits on the swap positions. -/
lemma ntBeta_occur {n j : ℕ} (hj : j + 1 ≤ n) {P Q : Fin n} (hPQ : P ≠ Q)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hj * Equiv.swap P Q)
    {i1 i2 i3 i4 : Fin n}
    (h12 : i1.val < i2.val) (h23 : i2.val < i3.val) (h34 : i3.val < i4.val)
    (hpat : ((κ i1 < κ i2 ∧ κ i2 < κ i3 ∧ κ i3 < κ i4) ∨
      (κ i3 < κ i4 ∧ κ i4 < κ i1 ∧ κ i1 < κ i2))) :
    (P = i1 ∧ Q = i3) ∨ (P = i3 ∧ Q = i1) ∨
    (P = i2 ∧ Q = i4) ∨ (P = i4 ∧ Q = i2) := by
  have d12 : i1 ≠ i2 := by intro h; subst h; exact lt_irrefl _ h12
  have d13 : i1 ≠ i3 := by
    intro h; subst h; exact lt_irrefl _ (lt_trans h12 h23)
  have d14 : i1 ≠ i4 := by
    intro h; subst h; exact lt_irrefl _ (lt_trans h12 (lt_trans h23 h34))
  have d23 : i2 ≠ i3 := by intro h; subst h; exact lt_irrefl _ h23
  have d24 : i2 ≠ i4 := by
    intro h; subst h; exact lt_irrefl _ (lt_trans h23 h34)
  have d34 : i3 ≠ i4 := by intro h; subst h; exact lt_irrefl _ h34
  have h13 : i1.val < i3.val := lt_trans h12 h23
  have h24 : i2.val < i4.val := lt_trans h23 h34
  have key : ∀ R S : Fin n, κ = ntBeta n j hj * Equiv.swap R S →
      (i1 = R ∨ i2 = R ∨ i3 = R ∨ i4 = R) := by
    intro R S hRS
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨n1, n2, n3, n4⟩ := hcon
    have hag : ∀ w : Fin n, w ≠ R → w ≠ S → κ w = (ntBeta n j hj) w := by
      intro w hwR hwS
      rw [hRS, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwR hwS]
    have a1 : i1 ≠ S → κ i1 = (ntBeta n j hj) i1 := fun h => hag i1 n1 h
    have a2 : i2 ≠ S → κ i2 = (ntBeta n j hj) i2 := fun h => hag i2 n2 h
    have a3 : i3 ≠ S → κ i3 = (ntBeta n j hj) i3 := fun h => hag i3 n3 h
    have a4 : i4 ≠ S → κ i4 = (ntBeta n j hj) i4 := fun h => hag i4 n4 h
    rcases hpat with h1234 | h3412
    · obtain ⟨g12, g23, g34⟩ := h1234
      rcases eq_or_ne S i1 with hS1|hS1
      · subst S
        have e2 := a2 (Ne.symm d12)
        have e3 := a3 (Ne.symm d13)
        have e4 := a4 (Ne.symm d14)
        rw [e2, e3] at g23
        rw [e3, e4] at g34
        exact ntBeta_no123 hj ⟨i2, i3, i4, h23, h34, g23, g34⟩
      · rcases eq_or_ne S i2 with hS2|hS2
        · subst S
          have e1 := a1 d12
          have e3 := a3 (Ne.symm d23)
          have e4 := a4 (Ne.symm d24)
          have h := lt_trans g12 g23
          rw [e1, e3] at h
          rw [e3, e4] at g34
          exact ntBeta_no123 hj ⟨i1, i3, i4, h13, h34, h, g34⟩
        · rcases eq_or_ne S i3 with hS3|hS3
          · subst S
            have e1 := a1 d13
            have e2 := a2 d23
            have e4 := a4 (Ne.symm d34)
            rw [e1, e2] at g12
            have h := lt_trans g23 g34
            rw [e2, e4] at h
            exact ntBeta_no123 hj ⟨i1, i2, i4, h12, h24, g12, h⟩
          · rcases eq_or_ne S i4 with hS4|hS4
            · subst S
              have e1 := a1 d14
              have e2 := a2 d24
              have e3 := a3 d34
              rw [e1, e2] at g12
              rw [e2, e3] at g23
              exact ntBeta_no123 hj ⟨i1, i2, i3, h12, h23, g12, g23⟩
            · have e1 := a1 (Ne.symm hS1)
              have e2 := a2 (Ne.symm hS2)
              have e3 := a3 (Ne.symm hS3)
              have e4 := a4 (Ne.symm hS4)
              rw [e1, e2] at g12
              rw [e2, e3] at g23
              exact ntBeta_no123 hj ⟨i1, i2, i3, h12, h23, g12, g23⟩
    · obtain ⟨g31, g42, g13⟩ := h3412
      rcases eq_or_ne S i1 with hS1|hS1
      · subst S
        have e2 := a2 (Ne.symm d12)
        have e3 := a3 (Ne.symm d13)
        have e4 := a4 (Ne.symm d14)
        rw [e3, e4] at g31
        have h := lt_trans g42 g13
        rw [e4, e2] at h
        exact ntBeta_no312 hj ⟨i2, i3, i4, h23, h34, g31, h⟩
      · rcases eq_or_ne S i2 with hS2|hS2
        · subst S
          have e1 := a1 d12
          have e3 := a3 (Ne.symm d23)
          have e4 := a4 (Ne.symm d24)
          rw [e3, e4] at g31
          rw [e4, e1] at g42
          exact ntBeta_no312 hj ⟨i1, i3, i4, h13, h34, g31, g42⟩
        · rcases eq_or_ne S i3 with hS3|hS3
          · subst S
            have e1 := a1 d13
            have e2 := a2 d23
            have e4 := a4 (Ne.symm d34)
            rw [e4, e1] at g42
            rw [e1, e2] at g13
            exact ntBeta_no231 hj ⟨i1, i2, i4, h12, h24, g42, g13⟩
          · rcases eq_or_ne S i4 with hS4|hS4
            · subst S
              have e1 := a1 d14
              have e2 := a2 d24
              have e3 := a3 d34
              have h := lt_trans g31 g42
              rw [e3, e1] at h
              rw [e1, e2] at g13
              exact ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, h, g13⟩
            · have e1 := a1 (Ne.symm hS1)
              have e2 := a2 (Ne.symm hS2)
              have e3 := a3 (Ne.symm hS3)
              have e4 := a4 (Ne.symm hS4)
              have h := lt_trans g31 g42
              rw [e3, e1] at h
              rw [e1, e2] at g13
              exact ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, h, g13⟩
  have hP4 := key P Q hκ
  have hκ' : κ = ntBeta n j hj * Equiv.swap Q P := by rw [hκ, Equiv.swap_comm]
  have hQ4 := key Q P hκ'
  rcases hP4 with rfl|rfl|rfl|rfl
  · rcases hQ4 with rfl|rfl|rfl|rfl
    · exact (hPQ rfl).elim
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v2 : κ i2 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d13) (Ne.symm d23)]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d14) (Ne.symm d24)]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        exact False.elim (ntBeta_no123 hj ⟨i1, i3, i4, h13, h34, g23, g34⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v2 : κ i2 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d13) (Ne.symm d23)]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d14) (Ne.symm d24)]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        have l41 : (ntBeta n j hj) i4 < (ntBeta n j hj) i1 := lt_trans g42 g13
        exact False.elim (ntBeta_no312 hj ⟨i1, i3, i4, h13, h34, g31, l41⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d12) (d24)]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d13) (d34)]
        have v4 : κ i4 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        exact False.elim (ntBeta_no231 hj ⟨i2, i3, i4, h23, h34, g12, g23⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d12) (d24)]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d13) (d34)]
        have v4 : κ i4 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        have l12 : (ntBeta n j hj) i1 < (ntBeta n j hj) i2 := lt_trans g42 g13
        exact False.elim (ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, g31, l12⟩)
  · rcases hQ4 with rfl|rfl|rfl|rfl
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v2 : κ i2 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d23) (Ne.symm d13)]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d24) (Ne.symm d14)]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        exact False.elim (ntBeta_no123 hj ⟨i1, i3, i4, h13, h34, g23, g34⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v2 : κ i2 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d23) (Ne.symm d13)]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d24) (Ne.symm d14)]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        have l41 : (ntBeta n j hj) i4 < (ntBeta n j hj) i1 := lt_trans g42 g13
        exact False.elim (ntBeta_no312 hj ⟨i1, i3, i4, h13, h34, g31, l41⟩)
    · exact (hPQ rfl).elim
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d12 d13]
        have v2 : κ i2 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v3 : κ i3 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d24) (Ne.symm d34)]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        have l12 : (ntBeta n j hj) i1 < (ntBeta n j hj) i2 := lt_trans g12 g23
        exact False.elim (ntBeta_no123 hj ⟨i1, i2, i4, h12, h24, l12, g34⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d12 d13]
        have v2 : κ i2 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v3 : κ i3 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d24) (Ne.symm d34)]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        exact False.elim (ntBeta_no312 hj ⟨i1, i2, i4, h12, h24, g31, g42⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rcases hQ4 with rfl|rfl|rfl|rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d13 d12]
        have v2 : κ i2 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v3 : κ i3 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d34) (Ne.symm d24)]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        have l12 : (ntBeta n j hj) i1 < (ntBeta n j hj) i2 := lt_trans g12 g23
        exact False.elim (ntBeta_no123 hj ⟨i1, i2, i4, h12, h24, l12, g34⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d13 d12]
        have v2 : κ i2 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v3 : κ i3 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d34) (Ne.symm d24)]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        exact False.elim (ntBeta_no312 hj ⟨i1, i2, i4, h12, h24, g31, g42⟩)
    · exact (hPQ rfl).elim
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d13 d14]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d23 d24]
        have v3 : κ i3 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v4 : κ i4 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        have l23 : (ntBeta n j hj) i2 < (ntBeta n j hj) i3 := lt_trans g23 g34
        exact False.elim (ntBeta_no123 hj ⟨i1, i2, i3, h12, h23, g12, l23⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d13 d14]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d23 d24]
        have v3 : κ i3 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v4 : κ i4 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        exact False.elim (ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, g42, g13⟩)
  · rcases hQ4 with rfl|rfl|rfl|rfl
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d24) (Ne.symm d12)]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d34) (Ne.symm d13)]
        have v4 : κ i4 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        exact False.elim (ntBeta_no231 hj ⟨i2, i3, i4, h23, h34, g12, g23⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d24) (Ne.symm d12)]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d34) (Ne.symm d13)]
        have v4 : κ i4 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        have l12 : (ntBeta n j hj) i1 < (ntBeta n j hj) i2 := lt_trans g42 g13
        exact False.elim (ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, g31, l12⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d14 d13]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d24) (d23)]
        have v3 : κ i3 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v4 : κ i4 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        have l23 : (ntBeta n j hj) i2 < (ntBeta n j hj) i3 := lt_trans g23 g34
        exact False.elim (ntBeta_no123 hj ⟨i1, i2, i3, h12, h23, g12, l23⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d14 d13]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d24) (d23)]
        have v3 : κ i3 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v4 : κ i4 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        exact False.elim (ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, g42, g13⟩)
    · exact (hPQ rfl).elim

/-- Each `K` is closed under moves in both directions. -/
lemma ntK_closed {n j : ℕ} (_hn : 5 ≤ n) (_hj1 : 1 ≤ j) (hjn : j + 1 ≤ n)
    {κ τ : Equiv.Perm (Fin n)}
    (hκ : κ ∈ ntK n j hjn) (h : ntMove n κ τ ∨ ntMove n τ κ) :
    τ ∈ ntK n j hjn := by
  obtain ⟨⟨P, Q, hPQ, hκT⟩, _hκP⟩ := hκ
  rcases h with hmove | hmove
  · obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34, t1, t2, t3, t4,
      hrest⟩ := hmove
    have d12 : i1 ≠ i2 := by intro h; subst h; exact lt_irrefl _ h12
    have d14 : i1 ≠ i4 := by
      intro h; subst h; exact lt_irrefl _ (lt_trans h12 (lt_trans h23 h34))
    have d23 : i2 ≠ i3 := by intro h; subst h; exact lt_irrefl _ h23
    have d24 : i2 ≠ i4 := by
      intro h; subst h; exact lt_irrefl _ (lt_trans h23 h34)
    have d34 : i3 ≠ i4 := by intro h; subst h; exact lt_irrefl _ h34
    have d13 : i1 ≠ i3 := by
      intro h; subst h; exact absurd (lt_trans h12 h23) (lt_irrefl _)
    have heq : τ = κ * Equiv.swap i1 i3 * Equiv.swap i2 i4 :=
      ntMove_eq h12 h23 h34 s12 s23 s34 t1 t2 t3 t4 hrest
    have hpatκ : (κ i1 < κ i2 ∧ κ i2 < κ i3 ∧ κ i3 < κ i4) ∨
        (κ i3 < κ i4 ∧ κ i4 < κ i1 ∧ κ i1 < κ i2) :=
      Or.inl ⟨s12, s23, s34⟩
    have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34 hpatκ
    obtain ⟨c31, c42, c13⟩ :=
      ntMove_pat3412 h12 h23 h34 s12 s23 s34 t1 t2 t3 t4
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · subst P; subst Q
      have hτ : τ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        have e : κ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
            ntBeta n j hjn * Equiv.swap i2 i4 := by
          rw [hκT, mul_assoc (ntBeta n j hjn) (Equiv.swap i1 i3)
            (Equiv.swap i1 i3), Equiv.swap_mul_self, mul_one]
        rw [heq]
        exact e
      refine ⟨⟨i2, i4, d24, hτ⟩,
        Or.inr ⟨i1, i2, i3, i4, h12, h23, h34, c31, c42, c13⟩⟩
    · subst P; subst Q
      have hκT' : κ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        rw [hκT, Equiv.swap_comm]
      have hτ : τ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        have e : κ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
            ntBeta n j hjn * Equiv.swap i2 i4 := by
          rw [hκT', mul_assoc (ntBeta n j hjn) (Equiv.swap i1 i3)
            (Equiv.swap i1 i3), Equiv.swap_mul_self, mul_one]
        rw [heq]
        exact e
      refine ⟨⟨i2, i4, d24, hτ⟩,
        Or.inr ⟨i1, i2, i3, i4, h12, h23, h34, c31, c42, c13⟩⟩
    · subst P; subst Q
      have hcomm : Equiv.swap i2 i4 * Equiv.swap i1 i3 =
          Equiv.swap i1 i3 * Equiv.swap i2 i4 :=
        ntSwap_comm_disjoint (Ne.symm d12) (d23) (Ne.symm d14)
          (Ne.symm d34)
      have hτ : τ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        have e : κ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
            ntBeta n j hjn * Equiv.swap i1 i3 := by
          rw [hκT, mul_assoc (ntBeta n j hjn) (Equiv.swap i2 i4)
            (Equiv.swap i1 i3), hcomm,
            ← mul_assoc (ntBeta n j hjn) (Equiv.swap i1 i3)
            (Equiv.swap i2 i4),
            mul_assoc (ntBeta n j hjn * Equiv.swap i1 i3)
            (Equiv.swap i2 i4) (Equiv.swap i2 i4),
            Equiv.swap_mul_self, mul_one]
        rw [heq]
        exact e
      refine ⟨⟨i1, i3, d13, hτ⟩,
        Or.inr ⟨i1, i2, i3, i4, h12, h23, h34, c31, c42, c13⟩⟩
    · subst P; subst Q
      have hκT' : κ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        rw [hκT, Equiv.swap_comm]
      have hcomm : Equiv.swap i2 i4 * Equiv.swap i1 i3 =
          Equiv.swap i1 i3 * Equiv.swap i2 i4 :=
        ntSwap_comm_disjoint (Ne.symm d12) (d23) (Ne.symm d14)
          (Ne.symm d34)
      have hτ : τ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        have e : κ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
            ntBeta n j hjn * Equiv.swap i1 i3 := by
          rw [hκT', mul_assoc (ntBeta n j hjn) (Equiv.swap i2 i4)
            (Equiv.swap i1 i3), hcomm,
            ← mul_assoc (ntBeta n j hjn) (Equiv.swap i1 i3)
            (Equiv.swap i2 i4),
            mul_assoc (ntBeta n j hjn * Equiv.swap i1 i3)
            (Equiv.swap i2 i4) (Equiv.swap i2 i4),
            Equiv.swap_mul_self, mul_one]
        rw [heq]
        exact e
      refine ⟨⟨i1, i3, d13, hτ⟩,
        Or.inr ⟨i1, i2, i3, i4, h12, h23, h34, c31, c42, c13⟩⟩
  · obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34, t1, t2, t3, t4,
      hrest⟩ := hmove
    have d12 : i1 ≠ i2 := by intro h; subst h; exact lt_irrefl _ h12
    have d14 : i1 ≠ i4 := by
      intro h; subst h; exact lt_irrefl _ (lt_trans h12 (lt_trans h23 h34))
    have d23 : i2 ≠ i3 := by intro h; subst h; exact lt_irrefl _ h23
    have d24 : i2 ≠ i4 := by
      intro h; subst h; exact lt_irrefl _ (lt_trans h23 h34)
    have d34 : i3 ≠ i4 := by intro h; subst h; exact lt_irrefl _ h34
    have d13 : i1 ≠ i3 := by
      intro h; subst h; exact absurd (lt_trans h12 h23) (lt_irrefl _)
    have heq : κ = τ * Equiv.swap i1 i3 * Equiv.swap i2 i4 :=
      ntMove_eq h12 h23 h34 s12 s23 s34 t1 t2 t3 t4 hrest
    obtain ⟨c31, c42, c13⟩ :=
      ntMove_pat3412 h12 h23 h34 s12 s23 s34 t1 t2 t3 t4
    have hpatκ : (κ i1 < κ i2 ∧ κ i2 < κ i3 ∧ κ i3 < κ i4) ∨
        (κ i3 < κ i4 ∧ κ i4 < κ i1 ∧ κ i1 < κ i2) :=
      Or.inr ⟨c31, c42, c13⟩
    have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34 hpatκ
    have sq13 : Equiv.swap i1 i3 * Equiv.swap i1 i3 = 1 :=
      Equiv.swap_mul_self _ _
    have sq24 : Equiv.swap i2 i4 * Equiv.swap i2 i4 = 1 :=
      Equiv.swap_mul_self _ _
    have hcomm : Equiv.swap i1 i3 * Equiv.swap i2 i4 =
        Equiv.swap i2 i4 * Equiv.swap i1 i3 :=
      ntSwap_comm_disjoint d12 d14 (Ne.symm d23) d34
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · subst P; subst Q
      have h1 : τ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
          ntBeta n j hjn * Equiv.swap i1 i3 := by rw [← heq, hκT]
      have hstep : τ * Equiv.swap i2 i4 = ntBeta n j hjn :=
        ntSwap_cancel_mid sq13 hcomm h1
      have hτ : τ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        rw [← hstep, mul_assoc τ (Equiv.swap i2 i4) (Equiv.swap i2 i4), sq24,
          mul_one]
      refine ⟨⟨i2, i4, d24, hτ⟩,
        Or.inl ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩⟩
    · subst P; subst Q
      have hκT' : κ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        rw [hκT, Equiv.swap_comm]
      have h1 : τ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
          ntBeta n j hjn * Equiv.swap i1 i3 := by rw [← heq, hκT']
      have hstep : τ * Equiv.swap i2 i4 = ntBeta n j hjn :=
        ntSwap_cancel_mid sq13 hcomm h1
      have hτ : τ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        rw [← hstep, mul_assoc τ (Equiv.swap i2 i4) (Equiv.swap i2 i4), sq24,
          mul_one]
      refine ⟨⟨i2, i4, d24, hτ⟩,
        Or.inl ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩⟩
    · subst P; subst Q
      have h1 : τ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
          ntBeta n j hjn * Equiv.swap i2 i4 := by rw [← heq, hκT]
      have hstep : τ * Equiv.swap i1 i3 = ntBeta n j hjn :=
        ntSwap_cancel_end sq24 h1
      have hτ : τ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        rw [← hstep, mul_assoc τ (Equiv.swap i1 i3) (Equiv.swap i1 i3), sq13,
          mul_one]
      refine ⟨⟨i1, i3, d13, hτ⟩,
        Or.inl ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩⟩
    · subst P; subst Q
      have hκT' : κ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        rw [hκT, Equiv.swap_comm]
      have h1 : τ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
          ntBeta n j hjn * Equiv.swap i2 i4 := by rw [← heq, hκT']
      have hstep : τ * Equiv.swap i1 i3 = ntBeta n j hjn :=
        ntSwap_cancel_end sq24 h1
      have hτ : τ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        rw [← hstep, mul_assoc τ (Equiv.swap i1 i3) (Equiv.swap i1 i3), sq13,
          mul_one]
      refine ⟨⟨i1, i3, d13, hτ⟩,
        Or.inl ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩⟩

/-- Swapping adjacent positions of the two-block permutation yields no pattern. -/
lemma ntK_noPat_adjacent {n j : ℕ} (hj : j + 1 ≤ n) {P Q : Fin n}
    (hPQ : P ≠ Q) (hadj : Q.val = P.val + 1 ∨ P.val = Q.val + 1)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hj * Equiv.swap P Q) :
    ¬ ntPat n κ := by
  intro hpat
  rcases hpat with ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ <;>
      rw [hP, hQ] at hadj <;> omega
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inr ⟨g31, g42, g13⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ <;>
      rw [hP, hQ] at hadj <;> omega

/-- The high hub `beta * swap j (n-1)` has a 1234 pattern. -/
lemma ntK_highHub_pat {n j : ℕ} (hn : 5 ≤ n) (hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ n) (hj3 : j + 3 ≤ n)
    {J N1 : Fin n} (hJ : J.val = j) (hN1 : N1.val = n - 1) :
    ntPat n (ntBeta n j hjn * Equiv.swap J N1) := by
  have h0lt : 0 < n := by omega
  have hJ1lt : j + 1 < n := by omega
  have hZv : ((⟨0, h0lt⟩ : Fin n)).val = 0 := rfl
  have hJ1v : ((⟨j + 1, hJ1lt⟩ : Fin n)).val = j + 1 := rfl
  have dZJ : (⟨0, h0lt⟩ : Fin n) ≠ J := Fin.ne_of_val_ne (by omega)
  have dZN : (⟨0, h0lt⟩ : Fin n) ≠ N1 := Fin.ne_of_val_ne (by omega)
  have dJ1J : (⟨j + 1, hJ1lt⟩ : Fin n) ≠ J := Fin.ne_of_val_ne (by omega)
  have dJ1N : (⟨j + 1, hJ1lt⟩ : Fin n) ≠ N1 := Fin.ne_of_val_ne (by omega)
  have eJ : (ntBeta n j hjn * Equiv.swap J N1) J = ntBeta n j hjn N1 := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have eN : (ntBeta n j hjn * Equiv.swap J N1) N1 = ntBeta n j hjn J := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have v0 : ((ntBeta n j hjn * Equiv.swap J N1) (⟨0, h0lt⟩ : Fin n)).val =
      j - 1 := by
    rw [ntHub_val hjn _ dZJ dZN, ntBeta_val]
    rw [ite_eq_left (by omega : (⟨0, h0lt⟩ : Fin n).val < j)]
    simp only [Nat.sub_zero]
  have vJ : ((ntBeta n j hjn * Equiv.swap J N1) J).val = j := by
    have e : ((ntBeta n j hjn * Equiv.swap J N1) J).val =
        ((ntBeta n j hjn) N1).val := congrArg Fin.val eJ
    rw [e, ntBeta_val]
    rw [ite_eq_right (by omega : ¬ N1.val < j)]
    rw [hN1]
    have hnn := N1.is_lt
    omega
  have vJ1 : ((ntBeta n j hjn * Equiv.swap J N1) ⟨j + 1, hJ1lt⟩).val = n - 2 := by
    rw [ntHub_val hjn _ dJ1J dJ1N, ntBeta_val]
    rw [ite_eq_right (by omega : ¬ (⟨j + 1, hJ1lt⟩ : Fin n).val < j)]
    rw [hJ1v]
    have hnn : j + 1 < n := hJ1lt
    omega
  have vN : ((ntBeta n j hjn * Equiv.swap J N1) N1).val = n - 1 := by
    have e : ((ntBeta n j hjn * Equiv.swap J N1) N1).val =
        ((ntBeta n j hjn) J).val := congrArg Fin.val eN
    rw [e, ntBeta_val]
    rw [ite_eq_right (by omega : ¬ J.val < j)]
    rw [hJ]
    have hnn := N1.is_lt
    omega
  refine Or.inl ⟨(⟨0, h0lt⟩ : Fin n), J, ⟨j + 1, hJ1lt⟩, N1, by omega, by omega,
    by omega, by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega,
    by rw [Fin.lt_def]; omega⟩

/-- The low hub `beta * swap 0 (j-1)` has a 1234 pattern. -/
lemma ntK_lowHub_pat {n j : ℕ} (hn : 5 ≤ n)
    (hjn : j + 1 ≤ n) (hj3 : 3 ≤ j)
    {Z J1 : Fin n} (hZ : Z.val = 0) (hJ1 : J1.val = j - 1) :
    ntPat n (ntBeta n j hjn * Equiv.swap Z J1) := by
  have hOlt : 1 < n := by omega
  have hN1lt : n - 1 < n := by omega
  have hOv : ((⟨1, hOlt⟩ : Fin n)).val = 1 := rfl
  have hN1v : ((⟨n - 1, hN1lt⟩ : Fin n)).val = n - 1 := rfl
  have dOZ : (⟨1, hOlt⟩ : Fin n) ≠ Z := Fin.ne_of_val_ne (by omega)
  have dOJ : (⟨1, hOlt⟩ : Fin n) ≠ J1 := Fin.ne_of_val_ne (by omega)
  have dNZ : (⟨n - 1, hN1lt⟩ : Fin n) ≠ Z := Fin.ne_of_val_ne (by omega)
  have dNJ : (⟨n - 1, hN1lt⟩ : Fin n) ≠ J1 := Fin.ne_of_val_ne (by omega)
  have eZ : (ntBeta n j hjn * Equiv.swap Z J1) Z = ntBeta n j hjn J1 := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have eJ : (ntBeta n j hjn * Equiv.swap Z J1) J1 = ntBeta n j hjn Z := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have vZ : ((ntBeta n j hjn * Equiv.swap Z J1) Z).val = 0 := by
    have e : ((ntBeta n j hjn * Equiv.swap Z J1) Z).val =
        ((ntBeta n j hjn) J1).val := congrArg Fin.val eZ
    rw [e, ntBeta_val]
    rw [ite_eq_left (by omega : J1.val < j)]
    rw [hJ1]
    omega
  have vO : ((ntBeta n j hjn * Equiv.swap Z J1) ⟨1, hOlt⟩).val = j - 2 := by
    rw [ntHub_val hjn _ dOZ dOJ, ntBeta_val]
    rw [ite_eq_left (by omega : (⟨1, hOlt⟩ : Fin n).val < j)]
    rw [hOv]
    omega
  have vJ : ((ntBeta n j hjn * Equiv.swap Z J1) J1).val = j - 1 := by
    have e : ((ntBeta n j hjn * Equiv.swap Z J1) J1).val =
        ((ntBeta n j hjn) Z).val := congrArg Fin.val eJ
    rw [e, ntBeta_val]
    rw [ite_eq_left (by omega : Z.val < j)]
    rw [hZ]
    simp only [Nat.sub_zero]
  have vN : ((ntBeta n j hjn * Equiv.swap Z J1) ⟨n - 1, hN1lt⟩).val = j := by
    rw [ntHub_val hjn _ dNZ dNJ, ntBeta_val]
    rw [ite_eq_right (by omega : ¬ (⟨n - 1, hN1lt⟩ : Fin n).val < j)]
    rw [hN1v]
    have hnn : n - 1 < n := hN1lt
    omega
  refine Or.inl ⟨Z, ⟨1, hOlt⟩, J1, ⟨n - 1, hN1lt⟩, by omega, by omega,
    by omega, by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega,
    by rw [Fin.lt_def]; omega⟩

/-- A low non-adjacent pair moves to a mixed pair. -/
lemma ntK_lowMove {n j : ℕ} (hjn : j + 1 ≤ n)
    {P Q : Fin n} (hPlow : P.val < j) (hQlow : Q.val < j)
    (hPQ2 : P.val + 2 ≤ Q.val)
    {P1 J : Fin n} (hP1 : P1.val = P.val + 1) (hJ : J.val = j)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hjn * Equiv.swap P Q) :
    Relation.EqvGen (ntMove n) κ (ntBeta n j hjn * Equiv.swap P1 J) := by
  have dP1P : P1 ≠ P := Fin.ne_of_val_ne (by omega)
  have dPJ : P ≠ J := Fin.ne_of_val_ne (by omega)
  have dP1Q : P1 ≠ Q := Fin.ne_of_val_ne (by omega)
  have dP1J : P1 ≠ J := Fin.ne_of_val_ne (by omega)
  have dQJ : Q ≠ J := Fin.ne_of_val_ne (by omega)
  have h12 : P.val < P1.val := by omega
  have h23 : P1.val < Q.val := by omega
  have h34 : Q.val < J.val := by omega
  have vP : (κ P).val = j - 1 - Q.val := by
    have eP : κ P = ntBeta n j hjn Q := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [eP, ntBeta_val, ite_eq_left hQlow]
  have vP1 : (κ P1).val = j - 1 - P1.val := by
    have eP1 : κ P1 = ntBeta n j hjn P1 := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dP1P dP1Q]
    rw [eP1, ntBeta_val, ite_eq_left (by omega : P1.val < j)]
  have vQ : (κ Q).val = j - 1 - P.val := by
    have eQ : κ Q = ntBeta n j hjn P := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    rw [eQ, ntBeta_val, ite_eq_left hPlow]
  have vJ : (κ J).val = n - 1 := by
    have eJ : κ J = ntBeta n j hjn J := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dPJ.symm dQJ.symm]
    rw [eJ, ntBeta_val, ite_eq_right (by omega : ¬ J.val < j), hJ]
    have hle : j + 1 ≤ n := hjn
    omega
  have s12 : κ P < κ P1 := by rw [Fin.lt_def]; omega
  have s23 : κ P1 < κ Q := by rw [Fin.lt_def]; omega
  have s34 : κ Q < κ J := by rw [Fin.lt_def]; omega
  have hmove : ntMove n κ (κ * Equiv.swap P Q * Equiv.swap P1 J) :=
    ntMove_of_1234 h12 h23 h34 s12 s23 s34
  have hres : κ * Equiv.swap P Q * Equiv.swap P1 J =
      ntBeta n j hjn * Equiv.swap P1 J := by
    rw [hκ, mul_assoc (ntBeta n j hjn) (Equiv.swap P Q) (Equiv.swap P Q),
      Equiv.swap_mul_self, mul_one]
  rw [hres] at hmove
  exact Relation.EqvGen.rel _ _ hmove

/-- A high non-adjacent pair moves to a mixed pair. -/
lemma ntK_highMove {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n)
    {P Q : Fin n} (hPhigh : j ≤ P.val) (hQhigh : j ≤ Q.val)
    (hPQ2 : P.val + 2 ≤ Q.val)
    {J1 P1 : Fin n} (hJ1 : J1.val = j - 1) (hP1 : P1.val = P.val + 1)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hjn * Equiv.swap P Q) :
    Relation.EqvGen (ntMove n) κ (ntBeta n j hjn * Equiv.swap J1 P1) := by
  have dJ1P : J1 ≠ P := Fin.ne_of_val_ne (by omega)
  have dJ1Q : J1 ≠ Q := Fin.ne_of_val_ne (by omega)
  have dP1P : P1 ≠ P := Fin.ne_of_val_ne (by omega)
  have dP1Q : P1 ≠ Q := Fin.ne_of_val_ne (by omega)
  have h12 : J1.val < P.val := by omega
  have h23 : P.val < P1.val := by omega
  have h34 : P1.val < Q.val := by omega
  have vJ1 : (κ J1).val = 0 := by
    have eJ1 : κ J1 = ntBeta n j hjn J1 := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dJ1P dJ1Q]
    rw [eJ1, ntBeta_val, ite_eq_left (by omega : J1.val < j), hJ1]
    omega
  have vP : (κ P).val = n + j - 1 - Q.val := by
    have eP : κ P = ntBeta n j hjn Q := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have e : (κ P).val = ((ntBeta n j hjn) Q).val := congrArg Fin.val eP
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ Q.val < j)]
  have vP1 : (κ P1).val = n + j - 1 - P1.val := by
    have eP1 : κ P1 = ntBeta n j hjn P1 := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dP1P dP1Q]
    rw [eP1, ntBeta_val, ite_eq_right (by omega : ¬ P1.val < j)]
  have vQ : (κ Q).val = n + j - 1 - P.val := by
    have eQ : κ Q = ntBeta n j hjn P := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have e : (κ Q).val = ((ntBeta n j hjn) P).val := congrArg Fin.val eQ
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ P.val < j)]
  have s12 : κ J1 < κ P := by rw [Fin.lt_def]; omega
  have s23 : κ P < κ P1 := by rw [Fin.lt_def]; omega
  have s34 : κ P1 < κ Q := by rw [Fin.lt_def]; omega
  have hmove : ntMove n κ (κ * Equiv.swap J1 P1 * Equiv.swap P Q) :=
    ntMove_of_1234 h12 h23 h34 s12 s23 s34
  have hcomm : Equiv.swap P Q * Equiv.swap J1 P1 =
      Equiv.swap J1 P1 * Equiv.swap P Q :=
    ntSwap_comm_disjoint dJ1P.symm dP1P.symm dJ1Q.symm dP1Q.symm
  have hres : κ * Equiv.swap J1 P1 * Equiv.swap P Q =
      ntBeta n j hjn * Equiv.swap J1 P1 := by
    rw [hκ, mul_assoc (ntBeta n j hjn) (Equiv.swap P Q) (Equiv.swap J1 P1),
      hcomm, ← mul_assoc (ntBeta n j hjn) (Equiv.swap J1 P1)
      (Equiv.swap P Q),
      mul_assoc (ntBeta n j hjn * Equiv.swap J1 P1)
      (Equiv.swap P Q) (Equiv.swap P Q),
      Equiv.swap_mul_self, mul_one]
  rw [hres] at hmove
  exact Relation.EqvGen.rel _ _ hmove

/-- The low hub moves to any interior mixed pair. -/
lemma ntK_lowHubMove {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n)
    {Z J1 : Fin n} (hZ : Z.val = 0) (hJ1 : J1.val = j - 1)
    {U W : Fin n} (hU0 : 0 < U.val) (hUJ : U.val < j - 1) (hWJ : j ≤ W.val)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hjn * Equiv.swap Z J1) :
    Relation.EqvGen (ntMove n) κ (ntBeta n j hjn * Equiv.swap U W) := by
  have hWlt := W.is_lt
  have dUZ : U ≠ Z := Fin.ne_of_val_ne (by omega)
  have dUJ : U ≠ J1 := Fin.ne_of_val_ne (by omega)
  have dWZ : W ≠ Z := Fin.ne_of_val_ne (by omega)
  have dWJ1 : W ≠ J1 := Fin.ne_of_val_ne (by omega)
  have h12 : Z.val < U.val := by omega
  have h23 : U.val < J1.val := by omega
  have h34 : J1.val < W.val := by omega
  have vZ : (κ Z).val = 0 := by
    have eZ : κ Z = ntBeta n j hjn J1 := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have e : (κ Z).val = ((ntBeta n j hjn) J1).val := congrArg Fin.val eZ
    rw [e, ntBeta_val, ite_eq_left (by omega : J1.val < j), hJ1]
    omega
  have vU : (κ U).val = j - 1 - U.val := by
    have eU : κ U = ntBeta n j hjn U := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dUZ dUJ]
    rw [eU, ntBeta_val, ite_eq_left (by omega : U.val < j)]
  have vJ : (κ J1).val = j - 1 := by
    have eJ : κ J1 = ntBeta n j hjn Z := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have e : (κ J1).val = ((ntBeta n j hjn) Z).val := congrArg Fin.val eJ
    rw [e, ntBeta_val, ite_eq_left (by omega : Z.val < j), hZ]
    simp only [Nat.sub_zero]
  have vW : (κ W).val = n + j - 1 - W.val := by
    have eW : κ W = ntBeta n j hjn W := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dWZ dWJ1]
    rw [eW, ntBeta_val, ite_eq_right (by omega : ¬ W.val < j)]
  have s12 : κ Z < κ U := by rw [Fin.lt_def]; omega
  have s23 : κ U < κ J1 := by rw [Fin.lt_def]; omega
  have s34 : κ J1 < κ W := by rw [Fin.lt_def]; omega
  have hmove : ntMove n κ (κ * Equiv.swap Z J1 * Equiv.swap U W) :=
    ntMove_of_1234 h12 h23 h34 s12 s23 s34
  have hres : κ * Equiv.swap Z J1 * Equiv.swap U W =
      ntBeta n j hjn * Equiv.swap U W := by
    rw [hκ, mul_assoc (ntBeta n j hjn) (Equiv.swap Z J1) (Equiv.swap Z J1),
      Equiv.swap_mul_self, mul_one]
  rw [hres] at hmove
  exact Relation.EqvGen.rel _ _ hmove

/-- The high hub moves to any interior mixed pair. -/
lemma ntK_highHubMove {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n)
    {J N1 : Fin n} (hJ : J.val = j) (hN1 : N1.val = n - 1)
    {U W : Fin n} (hUJ : U.val < j) (hJW : j < W.val) (hWN : W.val < n - 1)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hjn * Equiv.swap J N1) :
    Relation.EqvGen (ntMove n) κ (ntBeta n j hjn * Equiv.swap U W) := by
  have dUJ : U ≠ J := Fin.ne_of_val_ne (by omega)
  have dUN : U ≠ N1 := Fin.ne_of_val_ne (by omega)
  have dWJ : W ≠ J := Fin.ne_of_val_ne (by omega)
  have dWN : W ≠ N1 := Fin.ne_of_val_ne (by omega)
  have h12 : U.val < J.val := by omega
  have h23 : J.val < W.val := by omega
  have h34 : W.val < N1.val := by omega
  have vU : (κ U).val = j - 1 - U.val := by
    have eU : κ U = ntBeta n j hjn U := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dUJ dUN]
    rw [eU, ntBeta_val, ite_eq_left hUJ]
  have vJ : (κ J).val = j := by
    have eJ : κ J = ntBeta n j hjn N1 := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have e : (κ J).val = ((ntBeta n j hjn) N1).val := congrArg Fin.val eJ
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ N1.val < j), hN1]
    have hnn := N1.is_lt
    omega
  have vW : (κ W).val = n + j - 1 - W.val := by
    have eW : κ W = ntBeta n j hjn W := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dWJ dWN]
    rw [eW, ntBeta_val, ite_eq_right (by omega : ¬ W.val < j)]
  have vN : (κ N1).val = n - 1 := by
    have eN : κ N1 = ntBeta n j hjn J := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have e : (κ N1).val = ((ntBeta n j hjn) J).val := congrArg Fin.val eN
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ J.val < j), hJ]
    have hnn := N1.is_lt
    omega
  have s12 : κ U < κ J := by rw [Fin.lt_def]; omega
  have s23 : κ J < κ W := by rw [Fin.lt_def]; omega
  have s34 : κ W < κ N1 := by rw [Fin.lt_def]; omega
  have hmove : ntMove n κ (κ * Equiv.swap U W * Equiv.swap J N1) :=
    ntMove_of_1234 h12 h23 h34 s12 s23 s34
  have hcomm : Equiv.swap J N1 * Equiv.swap U W =
      Equiv.swap U W * Equiv.swap J N1 :=
    ntSwap_comm_disjoint dUJ.symm dWJ.symm dUN.symm dWN.symm
  have hres : κ * Equiv.swap U W * Equiv.swap J N1 =
      ntBeta n j hjn * Equiv.swap U W := by
    rw [hκ, mul_assoc (ntBeta n j hjn) (Equiv.swap J N1) (Equiv.swap U W),
      hcomm, ← mul_assoc (ntBeta n j hjn) (Equiv.swap U W)
      (Equiv.swap J N1),
      mul_assoc (ntBeta n j hjn * Equiv.swap U W)
      (Equiv.swap J N1) (Equiv.swap J N1),
      Equiv.swap_mul_self, mul_one]
  rw [hres] at hmove
  exact Relation.EqvGen.rel _ _ hmove

/-- The extreme pair `(0, j)` has no pattern: `kappa` takes the maximum there. -/
lemma ntK_noPat_C1 {n j : ℕ} (hj : j + 1 ≤ n)
    {P Q : Fin n} (hPQ : P ≠ Q) (hP0 : P.val = 0) (hQj : Q.val = j)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hj * Equiv.swap P Q) :
    ¬ ntPat n κ := by
  have vP : (κ P).val = n - 1 := by
    have eP : κ P = ntBeta n j hj Q := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have e : (κ P).val = ((ntBeta n j hj) Q).val := congrArg Fin.val eP
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ Q.val < j), hQj]
    have hle : j + 1 ≤ n := hj
    omega
  intro hpat
  rcases hpat with ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
    have hi2 := (κ i2).is_lt
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [← hP] at g12
      rw [Fin.lt_def, vP] at g12
      omega
    · have h3 : i3.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h2 : i2.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h4 : i4.val = 0 := by rw [← hP]; exact hP0
      omega
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inr ⟨g31, g42, g13⟩)
    have hi2 := (κ i2).is_lt
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [← hP] at g13
      rw [Fin.lt_def, vP] at g13
      omega
    · have h3 : i3.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h2 : i2.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h4 : i4.val = 0 := by rw [← hP]; exact hP0
      omega

/-- The extreme pair `(0, n-1)` has no pattern. -/
lemma ntK_noPat_C2 {n j : ℕ} (hj1 : 1 ≤ j) (hj : j + 1 ≤ n)
    {P Q : Fin n} (hPQ : P ≠ Q) (hP0 : P.val = 0) (hQn : Q.val = n - 1)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hj * Equiv.swap P Q) :
    ¬ ntPat n κ := by
  have vP : (κ P).val = j := by
    have eP : κ P = ntBeta n j hj Q := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have e : (κ P).val = ((ntBeta n j hj) Q).val := congrArg Fin.val eP
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ Q.val < j), hQn]
    have hle : j + 1 ≤ n := hj
    have hnn := Q.is_lt
    omega
  have vQ : (κ Q).val = j - 1 := by
    have eQ : κ Q = ntBeta n j hj P := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have e : (κ Q).val = ((ntBeta n j hj) P).val := congrArg Fin.val eQ
    rw [e, ntBeta_val, ite_eq_left (by omega : P.val < j), hP0]
    simp only [Nat.sub_zero]
  intro hpat
  rcases hpat with ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · have g13 : κ i1 < κ i3 := lt_trans g12 g23
      rw [← hP, ← hQ] at g13
      rw [Fin.lt_def, vP, vQ] at g13
      omega
    · have h3 : i3.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h2 : i2.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h4 : i4.val = 0 := by rw [← hP]; exact hP0
      omega
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inr ⟨g31, g42, g13⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [← hQ] at g31
      rw [← hP] at g42
      rw [Fin.lt_def] at g31
      rw [Fin.lt_def] at g42
      rw [vQ] at g31
      rw [vP] at g42
      omega
    · have h3 : i3.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h2 : i2.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h4 : i4.val = 0 := by rw [← hP]; exact hP0
      omega

/-- The extreme pair `(j-1, n-1)` has no pattern: `kappa` takes the minimum. -/
lemma ntK_noPat_C4 {n j : ℕ} (hj1 : 1 ≤ j) (hj : j + 1 ≤ n)
    {P Q : Fin n} (hPQ : P ≠ Q) (hPj : P.val = j - 1) (hQn : Q.val = n - 1)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hj * Equiv.swap P Q) :
    ¬ ntPat n κ := by
  have vQ : (κ Q).val = 0 := by
    have eQ : κ Q = ntBeta n j hj P := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have e : (κ Q).val = ((ntBeta n j hj) P).val := congrArg Fin.val eQ
    rw [e, ntBeta_val, ite_eq_left (by omega : P.val < j), hPj]
    omega
  intro hpat
  rcases hpat with ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · have h3 : i3.val = n - 1 := by rw [← hQ]; exact hQn
      have hi4 := (i4).is_lt
      omega
    · have h1 : i1.val = n - 1 := by rw [← hQ]; exact hQn
      have hi2 := (i2).is_lt
      omega
    · rw [← hQ] at g34
      rw [Fin.lt_def, vQ] at g34
      omega
    · have h2 : i2.val = n - 1 := by rw [← hQ]; exact hQn
      have hi3 := (i3).is_lt
      omega
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inr ⟨g31, g42, g13⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · have h3 : i3.val = n - 1 := by rw [← hQ]; exact hQn
      have hi4 := (i4).is_lt
      omega
    · have h1 : i1.val = n - 1 := by rw [← hQ]; exact hQn
      have hi2 := (i2).is_lt
      omega
    · rw [← hQ] at g31
      rw [Fin.lt_def, vQ] at g31
      omega
    · have h2 : i2.val = n - 1 := by rw [← hQ]; exact hQn
      have hi3 := (i3).is_lt
      omega

/-- When both hubs are live, the low hub reaches the high hub via `(1, n-2)`. -/
lemma ntK_hubBridge {n j : ℕ} (hjn : j + 1 ≤ n) (hj3lo : 3 ≤ j)
    (hj3hi : j + 3 ≤ n)
    {Z J1 J N1 O N2 : Fin n} (hZ : Z.val = 0) (hJ1 : J1.val = j - 1)
    (hJ : J.val = j) (hN1 : N1.val = n - 1)
    (hO : O.val = 1) (hN2 : N2.val = n - 2) :
    Relation.EqvGen (ntMove n) (ntBeta n j hjn * Equiv.swap Z J1)
      (ntBeta n j hjn * Equiv.swap J N1) := by
  have hLowMid := ntK_lowHubMove (hj1 := by omega) hjn hZ hJ1 (U := O)
    (W := N2) (by omega) (by omega) (by omega) (rfl)
  have hHighMid := ntK_highHubMove (hj1 := by omega) hjn hJ hN1 (U := O)
    (W := N2) (by omega) (by omega) (by omega) (rfl)
  exact Relation.EqvGen.trans _ _ _ hLowMid
    (Relation.EqvGen.symm _ _ hHighMid)

/-- Hub reachability when `j ≤ 2`: every element routes via high moves. -/
lemma ntK_hub_high_narrow {n j : ℕ} (hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ n) (hj2 : j ≤ 2)
    {J N1 : Fin n} (hJ : J.val = j) (hN1 : N1.val = n - 1) :
    ∀ κ ∈ ntK n j hjn, Relation.EqvGen (ntMove n) κ
      (ntBeta n j hjn * Equiv.swap J N1) := by
  have hmix : ∀ {A B : Fin n}, A.val < j → j ≤ B.val →
      ∀ {μ : Equiv.Perm (Fin n)}, μ = ntBeta n j hjn * Equiv.swap A B →
        A ≠ B → ntPat n μ →
        Relation.EqvGen (ntMove n) μ (ntBeta n j hjn * Equiv.swap J N1) := by
    intro A B hAlow hBhigh μ hμT hAB hpat'
    by_cases hBj : B.val = j
    · by_cases hA0 : A.val = 0
      · exact absurd hpat' (ntK_noPat_C1 hjn hAB hA0 hBj hμT)
      · by_cases hAj : A.val = j - 1
        · have hadj : B.val = A.val + 1 := by omega
          exact absurd hpat' (ntK_noPat_adjacent hjn hAB (Or.inl hadj) hμT)
        · omega
    · by_cases hBn : B.val = n - 1
      · by_cases hA0 : A.val = 0
        · exact absurd hpat' (ntK_noPat_C2 hj1 hjn hAB hA0 hBn hμT)
        · by_cases hAj : A.val = j - 1
          · exact absurd hpat' (ntK_noPat_C4 hj1 hjn hAB hAj hBn hμT)
          · omega
      · have hBlt := B.is_lt
        have hBint : j < B.val ∧ B.val < n - 1 := by
          constructor <;> omega
        have hM4 := ntK_highHubMove hj1 hjn hJ hN1 (U := A) (W := B)
          hAlow hBint.1 hBint.2 (rfl)
        have hsym := Relation.EqvGen.symm _ _ hM4
        rw [hμT]
        exact hsym
  intro κ hκ
  obtain ⟨⟨P, Q, hPQ, hκT⟩, hpat⟩ := hκ
  by_cases hPlow : P.val < j <;> by_cases hQlow : Q.val < j
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        omega
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          omega
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ
  · exact hmix hPlow (by omega) hκT hPQ hpat
  · have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
      rw [hκT, Equiv.swap_comm]
    exact hmix hQlow (by omega) hκT' (Ne.symm hPQ) hpat
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        have hPhigh : j ≤ P.val := by omega
        have hQhigh : j ≤ Q.val := by omega
        have hJ1lt : j - 1 < n := by omega
        have hP1lt : P.val + 1 < n := by have hQlt := Q.is_lt; omega
        have hM2 := ntK_highMove hj1 hjn hPhigh hQhigh hgap
          (J1 := ⟨j - 1, hJ1lt⟩) (P1 := ⟨P.val + 1, hP1lt⟩) rfl rfl hκT
        have hA : (⟨j - 1, hJ1lt⟩ : Fin n).val < j := by
          have hv : ((⟨j - 1, hJ1lt⟩ : Fin n)).val = j - 1 := rfl
          omega
        have hB1 : j < (⟨P.val + 1, hP1lt⟩ : Fin n).val := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hB2 : (⟨P.val + 1, hP1lt⟩ : Fin n).val < n - 1 := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          have hQlt := Q.is_lt
          omega
        have hM4 := ntK_highHubMove hj1 hjn hJ hN1
          (U := ⟨j - 1, hJ1lt⟩) (W := ⟨P.val + 1, hP1lt⟩) hA hB1 hB2 (rfl)
        exact Relation.EqvGen.trans _ _ _ hM2
          (Relation.EqvGen.symm _ _ hM4)
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          have hQhigh : j ≤ Q.val := by omega
          have hPhigh : j ≤ P.val := by omega
          have hJ1lt : j - 1 < n := by omega
          have hP1lt : Q.val + 1 < n := by have hPlt := P.is_lt; omega
          have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
            rw [hκT, Equiv.swap_comm]
          have hM2 := ntK_highMove hj1 hjn hQhigh hPhigh hgap
            (J1 := ⟨j - 1, hJ1lt⟩) (P1 := ⟨Q.val + 1, hP1lt⟩) rfl rfl hκT'
          have hA : (⟨j - 1, hJ1lt⟩ : Fin n).val < j := by
            have hv : ((⟨j - 1, hJ1lt⟩ : Fin n)).val = j - 1 := rfl
            omega
          have hB1 : j < (⟨Q.val + 1, hP1lt⟩ : Fin n).val := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hB2 : (⟨Q.val + 1, hP1lt⟩ : Fin n).val < n - 1 := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            have hPlt := P.is_lt
            omega
          have hM4 := ntK_highHubMove hj1 hjn hJ hN1
            (U := ⟨j - 1, hJ1lt⟩) (W := ⟨Q.val + 1, hP1lt⟩) hA hB1 hB2 (rfl)
          exact Relation.EqvGen.trans _ _ _ hM2
            (Relation.EqvGen.symm _ _ hM4)
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ

/-- Hub reachability when `n - 2 ≤ j`: every element routes via low moves. -/
lemma ntK_hub_low {n j : ℕ} (hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ n) (hjn2 : n - 2 ≤ j)
    {Z J1 : Fin n} (hZ : Z.val = 0) (hJ1 : J1.val = j - 1) :
    ∀ κ ∈ ntK n j hjn, Relation.EqvGen (ntMove n) κ
      (ntBeta n j hjn * Equiv.swap Z J1) := by
  have hmix : ∀ {A B : Fin n}, A.val < j → j ≤ B.val →
      ∀ {μ : Equiv.Perm (Fin n)}, μ = ntBeta n j hjn * Equiv.swap A B →
        A ≠ B → ntPat n μ →
        Relation.EqvGen (ntMove n) μ (ntBeta n j hjn * Equiv.swap Z J1) := by
    intro A B hAlow hBhigh μ hμT hAB hpat'
    by_cases hBj : B.val = j
    · by_cases hA0 : A.val = 0
      · exact absurd hpat' (ntK_noPat_C1 hjn hAB hA0 hBj hμT)
      · by_cases hAj : A.val = j - 1
        · have hadj : B.val = A.val + 1 := by omega
          exact absurd hpat' (ntK_noPat_adjacent hjn hAB (Or.inl hadj) hμT)
        · have hA0' : 0 < A.val := by omega
          have hAj' : A.val < j - 1 := by omega
          have hBhigh' : j ≤ B.val := by omega
          have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1 (U := A) (W := B)
            hA0' hAj' hBhigh' (rfl)
          have hsym := Relation.EqvGen.symm _ _ hM3
          rw [hμT]
          exact hsym
    · by_cases hBn : B.val = n - 1
      · by_cases hA0 : A.val = 0
        · exact absurd hpat' (ntK_noPat_C2 hj1 hjn hAB hA0 hBn hμT)
        · by_cases hAj : A.val = j - 1
          · exact absurd hpat' (ntK_noPat_C4 hj1 hjn hAB hAj hBn hμT)
          · have hA0' : 0 < A.val := by omega
            have hAj' : A.val < j - 1 := by omega
            have hBhigh' : j ≤ B.val := by omega
            have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1 (U := A) (W := B)
              hA0' hAj' hBhigh' (rfl)
            have hsym := Relation.EqvGen.symm _ _ hM3
            rw [hμT]
            exact hsym
      · have hBlt := B.is_lt
        omega
  intro κ hκ
  obtain ⟨⟨P, Q, hPQ, hκT⟩, hpat⟩ := hκ
  by_cases hPlow : P.val < j <;> by_cases hQlow : Q.val < j
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        have hP1lt : P.val + 1 < n := by have hQlt := Q.is_lt; omega
        have hJlt : j < n := by omega
        have hM1 := ntK_lowMove hjn hPlow hQlow hgap
          (P1 := ⟨P.val + 1, hP1lt⟩) (J := ⟨j, hJlt⟩) rfl rfl hκT
        have hA : 0 < (⟨P.val + 1, hP1lt⟩ : Fin n).val := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hAj : (⟨P.val + 1, hP1lt⟩ : Fin n).val < j - 1 := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hBj : j ≤ (⟨j, hJlt⟩ : Fin n).val := by
          have hv : ((⟨j, hJlt⟩ : Fin n)).val = j := rfl
          omega
        have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1
          (U := ⟨P.val + 1, hP1lt⟩) (W := ⟨j, hJlt⟩) hA hAj hBj (rfl)
        exact Relation.EqvGen.trans _ _ _ hM1
          (Relation.EqvGen.symm _ _ hM3)
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          have hP1lt : Q.val + 1 < n := by have hPlt := P.is_lt; omega
          have hJlt : j < n := by omega
          have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
            rw [hκT, Equiv.swap_comm]
          have hM1 := ntK_lowMove hjn hQlow hPlow hgap
            (P1 := ⟨Q.val + 1, hP1lt⟩) (J := ⟨j, hJlt⟩) rfl rfl hκT'
          have hA : 0 < (⟨Q.val + 1, hP1lt⟩ : Fin n).val := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hAj : (⟨Q.val + 1, hP1lt⟩ : Fin n).val < j - 1 := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hBj : j ≤ (⟨j, hJlt⟩ : Fin n).val := by
            have hv : ((⟨j, hJlt⟩ : Fin n)).val = j := rfl
            omega
          have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1
            (U := ⟨Q.val + 1, hP1lt⟩) (W := ⟨j, hJlt⟩) hA hAj hBj (rfl)
          exact Relation.EqvGen.trans _ _ _ hM1
            (Relation.EqvGen.symm _ _ hM3)
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ
  · exact hmix hPlow (by omega) hκT hPQ hpat
  · have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
      rw [hκT, Equiv.swap_comm]
    exact hmix hQlow (by omega) hκT' (Ne.symm hPQ) hpat
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        have hQlt := Q.is_lt
        omega
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          have hPlt := P.is_lt
          omega
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ

/-- Hub reachability when `3 ≤ j` and `j + 3 ≤ n`: full scheme with bridge. -/
lemma ntK_hub_high_wide {n j : ℕ} (hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ n) (hj3lo : 3 ≤ j) (hj3hi : j + 3 ≤ n)
    {J N1 Z J1 O N2 : Fin n} (hJ : J.val = j) (hN1 : N1.val = n - 1)
    (hZ : Z.val = 0) (hJ1 : J1.val = j - 1)
    (hO : O.val = 1) (hN2 : N2.val = n - 2) :
    ∀ κ ∈ ntK n j hjn, Relation.EqvGen (ntMove n) κ
      (ntBeta n j hjn * Equiv.swap J N1) := by
  have hBridge := ntK_hubBridge hjn hj3lo hj3hi hZ hJ1 hJ hN1 hO hN2
  have hmix : ∀ {A B : Fin n}, A.val < j → j ≤ B.val →
      ∀ {μ : Equiv.Perm (Fin n)}, μ = ntBeta n j hjn * Equiv.swap A B →
        A ≠ B → ntPat n μ →
        Relation.EqvGen (ntMove n) μ (ntBeta n j hjn * Equiv.swap J N1) := by
    intro A B hAlow hBhigh μ hμT hAB hpat'
    by_cases hBj : B.val = j
    · by_cases hA0 : A.val = 0
      · exact absurd hpat' (ntK_noPat_C1 hjn hAB hA0 hBj hμT)
      · by_cases hAj : A.val = j - 1
        · have hadj : B.val = A.val + 1 := by omega
          exact absurd hpat' (ntK_noPat_adjacent hjn hAB (Or.inl hadj) hμT)
        · have hA0' : 0 < A.val := by omega
          have hAj' : A.val < j - 1 := by omega
          have hBhigh' : j ≤ B.val := by omega
          have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1 (U := A) (W := B)
            hA0' hAj' hBhigh' (rfl)
          have h1 := Relation.EqvGen.symm _ _ hM3
          rw [hμT]
          exact Relation.EqvGen.trans _ _ _ h1 hBridge
    · by_cases hBn : B.val = n - 1
      · by_cases hA0 : A.val = 0
        · exact absurd hpat' (ntK_noPat_C2 hj1 hjn hAB hA0 hBn hμT)
        · by_cases hAj : A.val = j - 1
          · exact absurd hpat' (ntK_noPat_C4 hj1 hjn hAB hAj hBn hμT)
          · have hA0' : 0 < A.val := by omega
            have hAj' : A.val < j - 1 := by omega
            have hBhigh' : j ≤ B.val := by omega
            have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1 (U := A) (W := B)
              hA0' hAj' hBhigh' (rfl)
            have h1 := Relation.EqvGen.symm _ _ hM3
            rw [hμT]
            exact Relation.EqvGen.trans _ _ _ h1 hBridge
      · have hBlt := B.is_lt
        have hBint : j < B.val ∧ B.val < n - 1 := by
          constructor <;> omega
        have hM4 := ntK_highHubMove hj1 hjn hJ hN1 (U := A) (W := B)
          hAlow hBint.1 hBint.2 (rfl)
        have hsym := Relation.EqvGen.symm _ _ hM4
        rw [hμT]
        exact hsym
  intro κ hκ
  obtain ⟨⟨P, Q, hPQ, hκT⟩, hpat⟩ := hκ
  by_cases hPlow : P.val < j <;> by_cases hQlow : Q.val < j
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        have hP1lt : P.val + 1 < n := by have hQlt := Q.is_lt; omega
        have hJlt : j < n := by omega
        have hM1 := ntK_lowMove hjn hPlow hQlow hgap
          (P1 := ⟨P.val + 1, hP1lt⟩) (J := ⟨j, hJlt⟩) rfl rfl hκT
        have hA : 0 < (⟨P.val + 1, hP1lt⟩ : Fin n).val := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hAj : (⟨P.val + 1, hP1lt⟩ : Fin n).val < j - 1 := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hBj : j ≤ (⟨j, hJlt⟩ : Fin n).val := by
          have hv : ((⟨j, hJlt⟩ : Fin n)).val = j := rfl
          omega
        have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1
          (U := ⟨P.val + 1, hP1lt⟩) (W := ⟨j, hJlt⟩) hA hAj hBj (rfl)
        exact Relation.EqvGen.trans _ _ _ hM1
          (Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ hM3) hBridge)
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          have hP1lt : Q.val + 1 < n := by have hPlt := P.is_lt; omega
          have hJlt : j < n := by omega
          have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
            rw [hκT, Equiv.swap_comm]
          have hM1 := ntK_lowMove hjn hQlow hPlow hgap
            (P1 := ⟨Q.val + 1, hP1lt⟩) (J := ⟨j, hJlt⟩) rfl rfl hκT'
          have hA : 0 < (⟨Q.val + 1, hP1lt⟩ : Fin n).val := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hAj : (⟨Q.val + 1, hP1lt⟩ : Fin n).val < j - 1 := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hBj : j ≤ (⟨j, hJlt⟩ : Fin n).val := by
            have hv : ((⟨j, hJlt⟩ : Fin n)).val = j := rfl
            omega
          have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1
            (U := ⟨Q.val + 1, hP1lt⟩) (W := ⟨j, hJlt⟩) hA hAj hBj (rfl)
          exact Relation.EqvGen.trans _ _ _ hM1
            (Relation.EqvGen.trans _ _ _
              (Relation.EqvGen.symm _ _ hM3) hBridge)
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ
  · exact hmix hPlow (by omega) hκT hPQ hpat
  · have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
      rw [hκT, Equiv.swap_comm]
    exact hmix hQlow (by omega) hκT' (Ne.symm hPQ) hpat
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        have hPhigh : j ≤ P.val := by omega
        have hQhigh : j ≤ Q.val := by omega
        have hJ1lt : j - 1 < n := by omega
        have hP1lt : P.val + 1 < n := by have hQlt := Q.is_lt; omega
        have hM2 := ntK_highMove hj1 hjn hPhigh hQhigh hgap
          (J1 := ⟨j - 1, hJ1lt⟩) (P1 := ⟨P.val + 1, hP1lt⟩) rfl rfl hκT
        have hA : (⟨j - 1, hJ1lt⟩ : Fin n).val < j := by
          have hv : ((⟨j - 1, hJ1lt⟩ : Fin n)).val = j - 1 := rfl
          omega
        have hB1 : j < (⟨P.val + 1, hP1lt⟩ : Fin n).val := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hB2 : (⟨P.val + 1, hP1lt⟩ : Fin n).val < n - 1 := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          have hQlt := Q.is_lt
          omega
        have hM4 := ntK_highHubMove hj1 hjn hJ hN1
          (U := ⟨j - 1, hJ1lt⟩) (W := ⟨P.val + 1, hP1lt⟩) hA hB1 hB2 (rfl)
        exact Relation.EqvGen.trans _ _ _ hM2
          (Relation.EqvGen.symm _ _ hM4)
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          have hQhigh : j ≤ Q.val := by omega
          have hPhigh : j ≤ P.val := by omega
          have hJ1lt : j - 1 < n := by omega
          have hP1lt : Q.val + 1 < n := by have hPlt := P.is_lt; omega
          have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
            rw [hκT, Equiv.swap_comm]
          have hM2 := ntK_highMove hj1 hjn hQhigh hPhigh hgap
            (J1 := ⟨j - 1, hJ1lt⟩) (P1 := ⟨Q.val + 1, hP1lt⟩) rfl rfl hκT'
          have hA : (⟨j - 1, hJ1lt⟩ : Fin n).val < j := by
            have hv : ((⟨j - 1, hJ1lt⟩ : Fin n)).val = j - 1 := rfl
            omega
          have hB1 : j < (⟨Q.val + 1, hP1lt⟩ : Fin n).val := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hB2 : (⟨Q.val + 1, hP1lt⟩ : Fin n).val < n - 1 := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            have hPlt := P.is_lt
            omega
          have hM4 := ntK_highHubMove hj1 hjn hJ hN1
            (U := ⟨j - 1, hJ1lt⟩) (W := ⟨Q.val + 1, hP1lt⟩) hA hB1 hB2 (rfl)
          exact Relation.EqvGen.trans _ _ _ hM2
            (Relation.EqvGen.symm _ _ hM4)
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ

/-- Each `K` has a hub reaching every element. -/
lemma ntK_hub {n j : ℕ} (hn : 5 ≤ n) (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n) :
    ∃ hub ∈ ntK n j hjn,
      ∀ κ ∈ ntK n j hjn, Relation.EqvGen (ntMove n) κ hub := by
  have hJlt : j < n := by omega
  have hN1lt : n - 1 < n := by omega
  have h0lt : 0 < n := by omega
  have hJ1lt : j - 1 < n := by omega
  have hOlt : 1 < n := by omega
  have hN2lt : n - 2 < n := by omega
  have hJv : ((⟨j, hJlt⟩ : Fin n)).val = j := rfl
  have hN1v : ((⟨n - 1, hN1lt⟩ : Fin n)).val = n - 1 := rfl
  have hZv : ((⟨0, h0lt⟩ : Fin n)).val = 0 := rfl
  have hJ1v : ((⟨j - 1, hJ1lt⟩ : Fin n)).val = j - 1 := rfl
  have hOv : ((⟨1, hOlt⟩ : Fin n)).val = 1 := rfl
  have hN2v : ((⟨n - 2, hN2lt⟩ : Fin n)).val = n - 2 := rfl
  by_cases hj3 : j + 3 ≤ n
  · refine ⟨ntBeta n j hjn * Equiv.swap ⟨j, hJlt⟩ ⟨n - 1, hN1lt⟩,
      ⟨⟨⟨j, hJlt⟩, ⟨n - 1, hN1lt⟩, ?_, rfl⟩, ?_⟩, ?_⟩
    · exact Fin.ne_of_val_ne (by omega)
    · exact ntK_highHub_pat hn hj1 hjn hj3 hJv hN1v
    · by_cases hj2 : j ≤ 2
      · exact ntK_hub_high_narrow hj1 hjn hj2 hJv hN1v
      · have hj3lo : 3 ≤ j := by omega
        exact ntK_hub_high_wide hj1 hjn hj3lo hj3
          hJv hN1v hZv hJ1v hOv hN2v
  · have hjn2 : n - 2 ≤ j := by omega
    have hj3lo : 3 ≤ j := by omega
    refine ⟨ntBeta n j hjn * Equiv.swap ⟨0, h0lt⟩ ⟨j - 1, hJ1lt⟩,
      ⟨⟨⟨0, h0lt⟩, ⟨j - 1, hJ1lt⟩, ?_, rfl⟩, ?_⟩, ?_⟩
    · exact Fin.ne_of_val_ne (by omega)
    · exact ntK_lowHub_pat hn hjn hj3lo hZv hJ1v
    · exact ntK_hub_low hj1 hjn hjn2 hZv hJ1v

/-- The residue class forced by the two-block shape. -/
lemma ntBeta_residue {n j : ℕ} (hj1 : 1 ≤ j) (hj : j + 1 ≤ n)
    (i : Fin n) :
    Nat.ModEq n (((ntBeta n j hj) i).val + i.val) (j - 1) := by
  rw [ntBeta_val hj]
  by_cases h : i.val < j
  · rw [ite_eq_left h]
    have e : j - 1 - i.val + i.val = j - 1 := by omega
    rw [e]
  · rw [ite_eq_right h]
    have e : n + j - 1 - i.val + i.val = n + j - 1 := by
      have := i.is_lt
      omega
    have e2 : n + j - 1 = n + (j - 1) := by omega
    rw [e, e2]
    change (n + (j - 1)) % n = (j - 1) % n
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]

/-- Different `K`s are disjoint. -/
lemma ntK_disjoint {n j k : ℕ} (hn : 5 ≤ n)
    (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n) (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n)
    (hjk : j ≠ k) : Disjoint (ntK n j hjn) (ntK n k hkn) := by
  rw [Set.disjoint_left]
  intro κ hκJ hκK
  obtain ⟨⟨P, Q, hPQ, hκTj⟩, _⟩ := hκJ
  obtain ⟨⟨P', Q', hPQ', hκTk⟩, _⟩ := hκK
  have hcard : ({P, Q, P', Q'} : Finset (Fin n)).card ≤ 4 :=
    calc ({P, Q, P', Q'} : Finset (Fin n)).card
        ≤ ({Q, P', Q'} : Finset (Fin n)).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ ((({P', Q'} : Finset (Fin n)).card + 1) + 1) :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) _
      _ ≤ ((((({Q'} : Finset (Fin n)).card + 1) + 1) + 1)) :=
          Nat.add_le_add_right
            (Nat.add_le_add_right (Finset.card_insert_le _ _) _) _
      _ = 4 := by simp
  have hne : ({P, Q, P', Q'} : Finset (Fin n)) ≠ Finset.univ := by
    intro hcon
    have hcc := congrArg Finset.card hcon
    rw [Finset.card_univ, Fintype.card_fin] at hcc
    omega
  have hss : ({P, Q, P', Q'} : Finset (Fin n)) ⊂ Finset.univ :=
    Finset.ssubset_univ_iff.mpr hne
  obtain ⟨i, -, hi⟩ := Finset.exists_of_ssubset hss
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  obtain ⟨hiP, hiQ, hiP', hiQ'⟩ := hi
  have eJ : κ i = ntBeta n j hjn i := by
    rw [hκTj, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hiP hiQ]
  have eK : κ i = ntBeta n k hkn i := by
    rw [hκTk, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hiP' hiQ']
  have eJv : (κ i).val = ((ntBeta n j hjn) i).val := congrArg Fin.val eJ
  have eKv : (κ i).val = ((ntBeta n k hkn) i).val := congrArg Fin.val eK
  have rJ := ntBeta_residue hj1 hjn i
  have rK := ntBeta_residue hk1 hkn i
  rw [← eJv] at rJ
  rw [← eKv] at rK
  have hmod : (j - 1) % n = (k - 1) % n := rJ.symm.trans rK
  rw [Nat.mod_eq_of_lt (show j - 1 < n by omega),
    Nat.mod_eq_of_lt (show k - 1 < n by omega)] at hmod
  omega

/-- Each `K` lies inside the extreme-avoiding set. -/
lemma ntK_sub_E {m j : ℕ} (hj1 : 1 ≤ j) (hjn : j + 1 ≤ m + 2) :
    ntK (m + 2) j hjn ⊆ ntE (m + 1) := by
  intro κ hκ
  obtain ⟨⟨P, Q, hPQ, hκT⟩, hκP⟩ := hκ
  have hlastv : (Fin.last (m + 1) : Fin (m + 2)).val = m + 1 := Fin.val_last _
  have h0v : ((0 : Fin (m + 2))).val = 0 := Fin.val_zero _
  have hc0 : ((0 : Fin (m + 2))).val < j := by rw [h0v]; omega
  have beta0 : ((ntBeta (m + 2) j hjn) 0).val = j - 1 := by
    rw [ntBeta_val hjn, ite_eq_left hc0, h0v, Nat.sub_zero]
  have hlastlt : ¬ ((Fin.last (m + 1) : Fin (m + 2))).val < j := by
    rw [hlastv]; omega
  have betaLast : ((ntBeta (m + 2) j hjn) (Fin.last (m + 1))).val = j := by
    rw [ntBeta_val hjn, ite_eq_right hlastlt, hlastv]
    omega
  constructor
  · intro h0
    have hmax : (κ 0).val = m + 1 := by rw [h0]; exact hlastv
    have h0mem : (0 : Fin (m + 2)) = P ∨ (0 : Fin (m + 2)) = Q := by
      by_contra hcon
      simp only [not_or] at hcon
      obtain ⟨nP, nQ⟩ := hcon
      have hS0 : Equiv.swap P Q (0 : Fin (m + 2)) = 0 :=
        Equiv.swap_apply_of_ne_of_ne nP nQ
      have e : κ 0 = ntBeta (m + 2) j hjn 0 := by
        rw [hκT, Equiv.Perm.mul_apply, hS0]
      have ev : (κ 0).val = j - 1 := by rw [e]; exact beta0
      rw [ev] at hmax
      omega
    rcases hκP with h1234 | h3412
    · obtain ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ := h1234
      have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
      rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i1).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g12
          have hle : (κ i2).val ≤ m + 1 := by
            have := (κ i2).is_lt; omega
          omega
        · rw [hQ] at h0'
          have hr : (κ i3).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g34
          have hle : (κ i4).val ≤ m + 1 := by
            have := (κ i4).is_lt; omega
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i3).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g34
          have hle : (κ i4).val ≤ m + 1 := by
            have := (κ i4).is_lt; omega
          omega
        · rw [hQ] at h0'
          have hr : (κ i1).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g12
          have hle : (κ i2).val ≤ m + 1 := by
            have := (κ i2).is_lt; omega
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i2).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i2).val < (κ i3).val := Fin.lt_def.mp g23
          have hle : (κ i3).val ≤ m + 1 := by
            have := (κ i3).is_lt; omega
          omega
        · rw [hQ] at h0'
          rw [← h0'] at h34
          rw [h0v] at h34
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          rw [← h0'] at h34
          rw [h0v] at h34
          omega
        · rw [hQ] at h0'
          have hr : (κ i2).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i2).val < (κ i3).val := Fin.lt_def.mp g23
          have hle : (κ i3).val ≤ m + 1 := by
            have := (κ i3).is_lt; omega
          omega
    · obtain ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩ := h3412
      have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34
        (Or.inr ⟨g31, g42, g13⟩)
      rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i1).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g13
          have hle : (κ i2).val ≤ m + 1 := by
            have := (κ i2).is_lt; omega
          omega
        · rw [hQ] at h0'
          have hr : (κ i3).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g31
          have hle : (κ i4).val ≤ m + 1 := by
            have := (κ i4).is_lt; omega
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i3).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g31
          have hle : (κ i4).val ≤ m + 1 := by
            have := (κ i4).is_lt; omega
          omega
        · rw [hQ] at h0'
          have hr : (κ i1).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g13
          have hle : (κ i2).val ≤ m + 1 := by
            have := (κ i2).is_lt; omega
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          rw [← h0'] at h12
          rw [h0v] at h12
          omega
        · rw [hQ] at h0'
          have hr : (κ i4).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i4).val < (κ i1).val := Fin.lt_def.mp g42
          have hle : (κ i1).val ≤ m + 1 := by
            have := (κ i1).is_lt; omega
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i4).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i4).val < (κ i1).val := Fin.lt_def.mp g42
          have hle : (κ i1).val ≤ m + 1 := by
            have := (κ i1).is_lt; omega
          omega
        · rw [hQ] at h0'
          rw [← h0'] at h12
          rw [h0v] at h12
          omega
  · intro hlast
    have hmin : (κ (Fin.last (m + 1))).val = 0 := by rw [hlast]; exact h0v
    have hlastmem : Fin.last (m + 1) = P ∨ Fin.last (m + 1) = Q := by
      by_contra hcon
      simp only [not_or] at hcon
      obtain ⟨nP, nQ⟩ := hcon
      have hSl : Equiv.swap P Q (Fin.last (m + 1)) = Fin.last (m + 1) :=
        Equiv.swap_apply_of_ne_of_ne nP nQ
      have e : κ (Fin.last (m + 1)) = ntBeta (m + 2) j hjn (Fin.last (m + 1)) := by
        rw [hκT, Equiv.Perm.mul_apply, hSl]
      have ev : (κ (Fin.last (m + 1))).val = j := by rw [e]; exact betaLast
      rw [ev] at hmin
      omega
    rcases hκP with h1234 | h3412
    · obtain ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ := h1234
      have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
      rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          rw [← hl'] at h12
          rw [hlastv] at h12
          have hle : i2.val ≤ m + 1 := by
            have := i2.is_lt; omega
          omega
        · rw [hQ] at hl'
          have hr : (κ i3).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i2).val < (κ i3).val := Fin.lt_def.mp g23
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i3).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i2).val < (κ i3).val := Fin.lt_def.mp g23
          omega
        · rw [hQ] at hl'
          rw [← hl'] at h12
          rw [hlastv] at h12
          have hle : i2.val ≤ m + 1 := by
            have := i2.is_lt; omega
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i2).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g12
          omega
        · rw [hQ] at hl'
          have hr : (κ i4).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g34
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i4).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g34
          omega
        · rw [hQ] at hl'
          have hr : (κ i2).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g12
          omega
    · obtain ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩ := h3412
      have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34
        (Or.inr ⟨g31, g42, g13⟩)
      rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i1).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i4).val < (κ i1).val := Fin.lt_def.mp g42
          omega
        · rw [hQ] at hl'
          rw [← hl'] at h34
          rw [hlastv] at h34
          have hle : i4.val ≤ m + 1 := by
            have := i4.is_lt; omega
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          rw [← hl'] at h34
          rw [hlastv] at h34
          have hle : i4.val ≤ m + 1 := by
            have := i4.is_lt; omega
          omega
        · rw [hQ] at hl'
          have hr : (κ i1).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i4).val < (κ i1).val := Fin.lt_def.mp g42
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i2).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g13
          omega
        · rw [hQ] at hl'
          have hr : (κ i4).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g31
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i4).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g31
          omega
        · rw [hQ] at hl'
          have hr : (κ i2).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g13
          omega

/-- An increasing 5-subsequence rules out every `K`. -/
lemma ntInc5_notK {k j : ℕ} (_hk : 5 ≤ k + 2) (_hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ k + 2) {σ : Equiv.Perm (Fin (k + 2))}
    (h : ntInc5 (k + 2) σ) : σ ∉ ntK (k + 2) j hjn := by
  intro hσ
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, vab, vbc, vcd, vde⟩ := h
  obtain ⟨⟨P, Q, _hPQ, hσT⟩, -⟩ := hσ
  have hac : a.val < c.val := lt_trans hab hbc
  have hbd : b.val < d.val := lt_trans hbc hcd
  have hce : c.val < e.val := lt_trans hcd hde
  have had : a.val < d.val := lt_trans hab hbd
  have hbe : b.val < e.val := lt_trans hbc hce
  have hae : a.val < e.val := lt_trans hab hbe
  have dab : a ≠ b := by intro h; subst h; exact lt_irrefl _ hab
  have dac : a ≠ c := by intro h; subst h; exact lt_irrefl _ hac
  have dad : a ≠ d := by intro h; subst h; exact lt_irrefl _ had
  have dae : a ≠ e := by intro h; subst h; exact lt_irrefl _ hae
  have dbc : b ≠ c := by intro h; subst h; exact lt_irrefl _ hbc
  have dbd : b ≠ d := by intro h; subst h; exact lt_irrefl _ hbd
  have dbe : b ≠ e := by intro h; subst h; exact lt_irrefl _ hbe
  have dcd : c ≠ d := by intro h; subst h; exact lt_irrefl _ hcd
  have dce : c ≠ e := by intro h; subst h; exact lt_irrefl _ hce
  have dde : d ≠ e := by intro h; subst h; exact lt_irrefl _ hde
  have hag : ∀ w : Fin (k + 2), w ≠ P → w ≠ Q →
      σ w = (ntBeta (k + 2) j hjn) w := by
    intro w hwP hwQ
    rw [hσT, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwP hwQ]
  by_cases hP : P ∈ ({a, b, c, d, e} : Finset (Fin (k + 2)))
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with hPa | hPb | hPc | hPd | hPe
    · subst P
      by_cases hQ : Q ∈ ({b, c, d, e} : Finset (Fin (k + 2)))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with hQb | hQc | hQd | hQe
        · subst Q
          have e3 := hag c (Ne.symm dac) (Ne.symm dbc)
          have e4 := hag d (Ne.symm dad) (Ne.symm dbd)
          have e5 := hag e (Ne.symm dae) (Ne.symm dbe)
          have l1 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨c, d, e, hcd, hde, l1, l2⟩
        · subst Q
          have e2 := hag b (Ne.symm dab) dbc
          have e4 := hag d (Ne.symm dad) (Ne.symm dcd)
          have e5 := hag e (Ne.symm dae) (Ne.symm dce)
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
            rw [← e2, ← e4]; exact lt_trans vbc vcd
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨b, d, e, hbd, hde, l1, l2⟩
        · subst Q
          have e2 := hag b (Ne.symm dab) dbd
          have e3 := hag c (Ne.symm dac) dcd
          have e5 := hag e (Ne.symm dae) (Ne.symm dde)
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) e := by
            rw [← e3, ← e5]; exact lt_trans vcd vde
          exact ntBeta_no123 hjn ⟨b, c, e, hbc, hce, l1, l2⟩
        · subst Q
          have e2 := hag b (Ne.symm dab) dbe
          have e3 := hag c (Ne.symm dac) dce
          have e4 := hag d (Ne.symm dad) dde
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          exact ntBeta_no123 hjn ⟨b, c, d, hbc, hcd, l1, l2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        obtain ⟨hQb, hQc, hQd, hQe⟩ := hQ
        have e2 := hag b (Ne.symm dab) (Ne.symm hQb)
        have e3 := hag c (Ne.symm dac) (Ne.symm hQc)
        have e4 := hag d (Ne.symm dad) (Ne.symm hQd)
        have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
          rw [← e3, ← e4]; exact vcd
        exact ntBeta_no123 hjn ⟨b, c, d, hbc, hcd, l1, l2⟩
    · subst P
      by_cases hQ : Q ∈ ({a, c, d, e} : Finset (Fin (k + 2)))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with hQa | hQc | hQd | hQe
        · subst Q
          have e3 := hag c (Ne.symm dbc) (Ne.symm dac)
          have e4 := hag d (Ne.symm dbd) (Ne.symm dad)
          have e5 := hag e (Ne.symm dbe) (Ne.symm dae)
          have l1 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨c, d, e, hcd, hde, l1, l2⟩
        · subst Q
          have e1 := hag a dab dac
          have e4 := hag d (Ne.symm dbd) (Ne.symm dcd)
          have e5 := hag e (Ne.symm dbe) (Ne.symm dce)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) d := by
            rw [← e1, ← e4]; exact lt_trans vab (lt_trans vbc vcd)
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨a, d, e, had, hde, l1, l2⟩
        · subst Q
          have e1 := hag a dab dad
          have e3 := hag c (Ne.symm dbc) dcd
          have e5 := hag e (Ne.symm dbe) (Ne.symm dde)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
            rw [← e1, ← e3]; exact lt_trans vab vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) e := by
            rw [← e3, ← e5]; exact lt_trans vcd vde
          exact ntBeta_no123 hjn ⟨a, c, e, hac, hce, l1, l2⟩
        · subst Q
          have e1 := hag a dab dae
          have e3 := hag c (Ne.symm dbc) dce
          have e4 := hag d (Ne.symm dbd) dde
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
            rw [← e1, ← e3]; exact lt_trans vab vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          exact ntBeta_no123 hjn ⟨a, c, d, hac, hcd, l1, l2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        obtain ⟨hQa, hQc, hQd, hQe⟩ := hQ
        have e1 := hag a dab (Ne.symm hQa)
        have e3 := hag c (Ne.symm dbc) (Ne.symm hQc)
        have e4 := hag d (Ne.symm dbd) (Ne.symm hQd)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
          rw [← e1, ← e3]; exact lt_trans vab vbc
        have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
          rw [← e3, ← e4]; exact vcd
        exact ntBeta_no123 hjn ⟨a, c, d, hac, hcd, l1, l2⟩
    · subst P
      by_cases hQ : Q ∈ ({a, b, d, e} : Finset (Fin (k + 2)))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with hQa | hQb | hQd | hQe
        · subst Q
          have e2 := hag b dbc (Ne.symm dab)
          have e4 := hag d (Ne.symm dcd) (Ne.symm dad)
          have e5 := hag e (Ne.symm dce) (Ne.symm dae)
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
            rw [← e2, ← e4]; exact lt_trans vbc vcd
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨b, d, e, hbd, hde, l1, l2⟩
        · subst Q
          have e1 := hag a dac dab
          have e4 := hag d (Ne.symm dcd) (Ne.symm dbd)
          have e5 := hag e (Ne.symm dce) (Ne.symm dbe)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) d := by
            rw [← e1, ← e4]; exact lt_trans vab (lt_trans vbc vcd)
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨a, d, e, had, hde, l1, l2⟩
        · subst Q
          have e1 := hag a dac dad
          have e2 := hag b dbc dbd
          have e5 := hag e (Ne.symm dce) (Ne.symm dde)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) e := by
            rw [← e2, ← e5]; exact lt_trans vbc (lt_trans vcd vde)
          exact ntBeta_no123 hjn ⟨a, b, e, hab, hbe, l1, l2⟩
        · subst Q
          have e1 := hag a dac dae
          have e2 := hag b dbc dbe
          have e4 := hag d (Ne.symm dcd) dde
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
            rw [← e2, ← e4]; exact lt_trans vbc vcd
          exact ntBeta_no123 hjn ⟨a, b, d, hab, hbd, l1, l2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        obtain ⟨hQa, hQb, hQd, hQe⟩ := hQ
        have e1 := hag a dac (Ne.symm hQa)
        have e2 := hag b dbc (Ne.symm hQb)
        have e4 := hag d (Ne.symm dcd) (Ne.symm hQd)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
          rw [← e2, ← e4]; exact lt_trans vbc vcd
        exact ntBeta_no123 hjn ⟨a, b, d, hab, hbd, l1, l2⟩
    · subst P
      by_cases hQ : Q ∈ ({a, b, c, e} : Finset (Fin (k + 2)))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with hQa | hQb | hQc | hQe
        · subst Q
          have e2 := hag b dbd (Ne.symm dab)
          have e3 := hag c dcd (Ne.symm dac)
          have e5 := hag e (Ne.symm dde) (Ne.symm dae)
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) e := by
            rw [← e3, ← e5]; exact lt_trans vcd vde
          exact ntBeta_no123 hjn ⟨b, c, e, hbc, hce, l1, l2⟩
        · subst Q
          have e1 := hag a dad dab
          have e3 := hag c dcd (Ne.symm dbc)
          have e5 := hag e (Ne.symm dde) (Ne.symm dbe)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
            rw [← e1, ← e3]; exact lt_trans vab vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) e := by
            rw [← e3, ← e5]; exact lt_trans vcd vde
          exact ntBeta_no123 hjn ⟨a, c, e, hac, hce, l1, l2⟩
        · subst Q
          have e1 := hag a dad dac
          have e2 := hag b dbd dbc
          have e5 := hag e (Ne.symm dde) (Ne.symm dce)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) e := by
            rw [← e2, ← e5]; exact lt_trans vbc (lt_trans vcd vde)
          exact ntBeta_no123 hjn ⟨a, b, e, hab, hbe, l1, l2⟩
        · subst Q
          have e1 := hag a dad dae
          have e2 := hag b dbd dbe
          have e3 := hag c dcd dce
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        obtain ⟨hQa, hQb, hQc, hQe⟩ := hQ
        have e1 := hag a dad (Ne.symm hQa)
        have e2 := hag b dbd (Ne.symm hQb)
        have e3 := hag c dcd (Ne.symm hQc)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
    · subst P
      by_cases hQ : Q ∈ ({a, b, c, d} : Finset (Fin (k + 2)))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with hQa | hQb | hQc | hQd
        · subst Q
          have e2 := hag b dbe (Ne.symm dab)
          have e3 := hag c dce (Ne.symm dac)
          have e4 := hag d dde (Ne.symm dad)
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          exact ntBeta_no123 hjn ⟨b, c, d, hbc, hcd, l1, l2⟩
        · subst Q
          have e1 := hag a dae dab
          have e3 := hag c dce (Ne.symm dbc)
          have e4 := hag d dde (Ne.symm dbd)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
            rw [← e1, ← e3]; exact lt_trans vab vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          exact ntBeta_no123 hjn ⟨a, c, d, hac, hcd, l1, l2⟩
        · subst Q
          have e1 := hag a dae dac
          have e2 := hag b dbe dbc
          have e4 := hag d dde (Ne.symm dcd)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
            rw [← e2, ← e4]; exact lt_trans vbc vcd
          exact ntBeta_no123 hjn ⟨a, b, d, hab, hbd, l1, l2⟩
        · subst Q
          have e1 := hag a dae dad
          have e2 := hag b dbe dbd
          have e3 := hag c dce dcd
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        obtain ⟨hQa, hQb, hQc, hQd⟩ := hQ
        have e1 := hag a dae (Ne.symm hQa)
        have e2 := hag b dbe (Ne.symm hQb)
        have e3 := hag c dce (Ne.symm hQc)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hP
    obtain ⟨hPa, hPb, hPc, hPd, hPe⟩ := hP
    by_cases hQ : Q ∈ ({a, b, c, d, e} : Finset (Fin (k + 2)))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
      rcases hQ with hQa | hQb | hQc | hQd | hQe
      · subst Q
        have e2 := hag b (Ne.symm hPb) (Ne.symm dab)
        have e3 := hag c (Ne.symm hPc) (Ne.symm dac)
        have e4 := hag d (Ne.symm hPd) (Ne.symm dad)
        have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
          rw [← e3, ← e4]; exact vcd
        exact ntBeta_no123 hjn ⟨b, c, d, hbc, hcd, l1, l2⟩
      · subst Q
        have e1 := hag a (Ne.symm hPa) dab
        have e3 := hag c (Ne.symm hPc) (Ne.symm dbc)
        have e4 := hag d (Ne.symm hPd) (Ne.symm dbd)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
          rw [← e1, ← e3]; exact lt_trans vab vbc
        have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
          rw [← e3, ← e4]; exact vcd
        exact ntBeta_no123 hjn ⟨a, c, d, hac, hcd, l1, l2⟩
      · subst Q
        have e1 := hag a (Ne.symm hPa) dac
        have e2 := hag b (Ne.symm hPb) dbc
        have e4 := hag d (Ne.symm hPd) (Ne.symm dcd)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
          rw [← e2, ← e4]; exact lt_trans vbc vcd
        exact ntBeta_no123 hjn ⟨a, b, d, hab, hbd, l1, l2⟩
      · subst Q
        have e1 := hag a (Ne.symm hPa) dad
        have e2 := hag b (Ne.symm hPb) dbd
        have e3 := hag c (Ne.symm hPc) dcd
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
      · subst Q
        have e1 := hag a (Ne.symm hPa) dae
        have e2 := hag b (Ne.symm hPb) dbe
        have e3 := hag c (Ne.symm hPc) dce
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
      obtain ⟨hQa, hQb, hQc, hQd, hQe⟩ := hQ
      have e1 := hag a (Ne.symm hPa) (Ne.symm hQa)
      have e2 := hag b (Ne.symm hPb) (Ne.symm hQb)
      have e3 := hag c (Ne.symm hPc) (Ne.symm hQc)
      have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
        rw [← e1, ← e2]; exact vab
      have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
        rw [← e2, ← e3]; exact vbc
      exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩

/-- The `j = 0` swap family has no patterns: `beta_0` is the full reversal. -/
lemma ntK_zero_empty {n : ℕ} (hj : 0 + 1 ≤ n) :
    ntK n 0 hj = ∅ := by
  have hbetaLT : ∀ a b : Fin n,
      (ntBeta n 0 hj a < ntBeta n 0 hj b) ↔ (b.val < a.val) := by
    intro a b
    rw [Fin.lt_def, ntBeta_val hj, ntBeta_val hj]
    have ha := a.is_lt
    have hb := b.is_lt
    simp only [Nat.not_lt_zero, ite_false]
    omega
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨⟨P, Q, hPQ, hκ⟩, hpat⟩ := hz
  rcases hpat with ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
    have d12 : i1 ≠ i2 := Fin.ne_of_val_ne (by omega)
    have d13 : i1 ≠ i3 := Fin.ne_of_val_ne (by omega)
    have d14 : i1 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have d23 : i2 ≠ i3 := Fin.ne_of_val_ne (by omega)
    have d24 : i2 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have d34 : i3 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have h14 : i1.val < i4.val := lt_trans h12 (lt_trans h23 h34)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [hP, hQ] at hκ
      have e3 : z i3 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have e4 : z i4 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d14.symm d34.symm]
      have g34' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e3, ← e4]; exact g34)
      omega
    · rw [hP, hQ] at hκ
      have e3 : z i3 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have e4 : z i4 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d34.symm d14.symm]
      have g34' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e3, ← e4]; exact g34)
      omega
    · rw [hP, hQ] at hκ
      have e1 : z i1 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d12 d14]
      have e2 : z i2 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have g12' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e1, ← e2]; exact g12)
      omega
    · rw [hP, hQ] at hκ
      have e1 : z i1 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d14 d12]
      have e2 : z i2 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have g12' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e1, ← e2]; exact g12)
      omega
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inr ⟨g31, g42, g13⟩)
    have d12 : i1 ≠ i2 := Fin.ne_of_val_ne (by omega)
    have d13 : i1 ≠ i3 := Fin.ne_of_val_ne (by omega)
    have d14 : i1 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have d23 : i2 ≠ i3 := Fin.ne_of_val_ne (by omega)
    have d24 : i2 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have d34 : i3 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have h14 : i1.val < i4.val := lt_trans h12 (lt_trans h23 h34)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [hP, hQ] at hκ
      have e3 : z i3 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have e4 : z i4 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d14.symm d34.symm]
      have g31' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e3, ← e4]; exact g31)
      omega
    · rw [hP, hQ] at hκ
      have e3 : z i3 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have e4 : z i4 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d34.symm d14.symm]
      have g31' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e3, ← e4]; exact g31)
      omega
    · rw [hP, hQ] at hκ
      have e1 : z i1 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d12 d14]
      have e2 : z i2 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have g13' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e1, ← e2]; exact g13)
      omega
    · rw [hP, hQ] at hκ
      have e1 : z i1 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d14 d12]
      have e2 : z i2 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have g13' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e1, ← e2]; exact g13)
      omega

/-- Generic elements from `inc5`: packaging `E`, pattern and non-`K` facts. -/
lemma ntMemG_of_inc5 {m : ℕ} (hm : 5 ≤ m) {σ : Equiv.Perm (Fin (m + 2))}
    (hE : σ ∈ ntE (m + 1)) (hinc : ntInc5 (m + 2) σ) : σ ∈ ntG (m + 1) := by
  refine ⟨hE, ntInc5_pat hinc, ?_⟩
  intro j hj hmem
  by_cases hj0 : j = 0
  · subst hj0
    rw [ntK_zero_empty hj] at hmem
    exact absurd hmem (Set.notMem_empty _)
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    exact ntInc5_notK (by omega) (by omega) hj hinc hmem

/-- The even reference permutation is generic. -/
lemma ntEven_memG {m : ℕ} (hm : 5 ≤ m) : ntEven (m + 2) ∈ ntG (m + 1) := by
  have hid : ∀ x : Fin (m + 2), ntEven (m + 2) x = x := fun x => rfl
  have h01 : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    intro hcon
    have hvv := congrArg Fin.val hcon
    simp only [Fin.val_zero, Fin.val_last] at hvv
    omega
  have hE : ntEven (m + 2) ∈ ntE (m + 1) := by
    constructor
    · change (1 : Equiv.Perm (Fin (m + 2))) 0 ≠ Fin.last (m + 1)
      exact h01
    · change (1 : Equiv.Perm (Fin (m + 2))) (Fin.last (m + 1)) ≠ 0
      exact fun h => h01 h.symm
  have hpat : ntPat (m + 2) (ntEven (m + 2)) := by
    refine Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
      by simp, by simp, by simp, ?_, ?_, ?_⟩
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
  have hinc : ntInc5 (m + 2) (ntEven (m + 2)) := by
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
      ⟨4, by omega⟩, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
  exact ntMemG_of_inc5 hm hE hinc

/-- The odd reference permutation is generic. -/
lemma ntOdd_memG {m : ℕ} (hm : 5 ≤ m) : ntOdd m ∈ ntG (m + 1) := by
  have hfix : ∀ x : Fin (m + 2), x.val ≤ 4 → ntOdd m x = x := by
    intro x hx
    unfold ntOdd
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hcon
      have hv : x.val = m := congrArg Fin.val hcon
      omega
    · intro hcon
      have hv : x.val = m + 1 := congrArg Fin.val hcon
      omega
  have hlast : Fin.last (m + 1) = (⟨m + 1, by omega⟩ : Fin (m + 2)) :=
    Fin.ext (Fin.val_last _)
  have h01 : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    intro hcon
    have hvv := congrArg Fin.val hcon
    simp only [Fin.val_zero, Fin.val_last] at hvv
    omega
  have hE : ntOdd m ∈ ntE (m + 1) := by
    constructor
    · have e0 : ntOdd m 0 = 0 := hfix 0 (by rw [Fin.val_zero]; omega)
      rw [e0]
      intro hcon
      have hvv := congrArg Fin.val hcon
      simp only [Fin.val_zero, Fin.val_last] at hvv
      omega
    · rw [hlast]
      intro hcon
      have e : ntOdd m (⟨m + 1, by omega⟩ : Fin (m + 2)) =
          (⟨m, by omega⟩ : Fin (m + 2)) := Equiv.swap_apply_right _ _
      have h2 : (⟨m, by omega⟩ : Fin (m + 2)) = 0 := e.symm.trans hcon
      have hmv : m = 0 := congrArg Fin.val h2
      omega
  have hpat : ntPat (m + 2) (ntOdd m) := by
    refine Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
      by simp, by simp, by simp, ?_, ?_, ?_⟩
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
  have hinc : ntInc5 (m + 2) (ntOdd m) := by
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
      ⟨4, by omega⟩, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
  exact ntMemG_of_inc5 hm hE hinc

/-- Insertions into the identity at non-inert positions are generic. -/
lemma ntG_id_ins {m : ℕ} (hm : 5 ≤ m) (y' v' : Fin (m + 2))
    (hne : (y' ≠ 0 ∨ v' ≠ Fin.last (m + 1)) ∧
      (y' ≠ Fin.last (m + 1) ∨ v' ≠ 0)) :
    ntIns y' v' 1 ∈ ntG (m + 1) :=
  ntMemG_of_inc5 hm (ntIns_memE y' v' 1 rfl hne) (ntInc5_id_ins hm y' v')

/-- Insertions into the `2-3` swap at non-inert positions are generic. -/
lemma ntG_swap23_ins {m : ℕ} (hm : 5 ≤ m) (y' v' : Fin (m + 2))
    (μ : Equiv.Perm (Fin (m + 1)))
    (hμ : μ = Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩)
    (hne : (y' ≠ 0 ∨ v' ≠ Fin.last (m + 1)) ∧
      (y' ≠ Fin.last (m + 1) ∨ v' ≠ 0)) :
    ntIns y' v' μ ∈ ntG (m + 1) := by
  have hμ0 : μ 0 = 0 := by
    rw [hμ]
    exact ntSwap_fix_vals _ _ _ (by simp) (by simp)
  exact ntMemG_of_inc5 hm (ntIns_memE _ _ _ hμ0 hne)
    (ntInc5_swap23_ins hm y' v' μ hμ)

/-- Branch 1: insertions at positive positions land in a reference class. -/
lemma ntIns_branch1 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {y v : Fin (m + 3)} {ρ : Equiv.Perm (Fin (m + 2))}
    (hρ : ρ ∈ ntG (m + 1))
    (hy1 : 1 ≤ y.val) (hv1 : 1 ≤ v.val)
    (hne1 : (y.val, v.val) ≠ (1, m + 2)) (hne2 : (y.val, v.val) ≠ (m + 2, 1)) :
    Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntOdd (m + 1)) := by
  have hy'lt : y.val < m + 3 := y.is_lt
  have hv'lt : v.val < m + 3 := v.is_lt
  set y' : Fin (m + 2) := ⟨y.val - 1, by omega⟩ with hy'def
  set v' : Fin (m + 2) := ⟨v.val - 1, by omega⟩ with hv'def
  have ey : y'.val = y.val - 1 := rfl
  have ev : v'.val = v.val - 1 := rfl
  have hy : y = y'.succ := by
    apply Fin.ext
    rw [Fin.val_succ]
    omega
  have hv : v = v'.succ := by
    apply Fin.ext
    rw [Fin.val_succ]
    omega
  have hne' : (y' ≠ 0 ∨ v' ≠ Fin.last (m + 1)) ∧
      (y' ≠ Fin.last (m + 1) ∨ v' ≠ 0) := by
    constructor
    · by_contra hc
      simp only [not_or, not_not] at hc
      obtain ⟨hy0, hv0⟩ := hc
      have h1 : y'.val = 0 := by rw [hy0]; exact Fin.val_zero _
      have h2 : v'.val = m + 1 := by rw [hv0]; exact Fin.val_last _
      have hyv : y.val = 1 := by omega
      have hvv : v.val = m + 2 := by omega
      exact hne1 (by rw [hyv, hvv])
    · by_contra hc
      simp only [not_or, not_not] at hc
      obtain ⟨hy0, hv0⟩ := hc
      have h1 : y'.val = m + 1 := by rw [hy0]; exact Fin.val_last _
      have h2 : v'.val = 0 := by rw [hv0]; exact Fin.val_zero _
      have hyv : y.val = m + 2 := by omega
      have hvv : v.val = 1 := by omega
      exact hne2 (by rw [hyv, hvv])
  rcases hIH ρ hρ with hρe | hρo
  · have hμ'G : ntEven (m + 2) ∈ ntG (m + 1) := ntEven_memG hm
    have hρμ : Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) :=
      ntG_sameSign hIH hρ hμ'G (ntEqvGen_sign hρe)
    have hcongr : Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ)
        (ntIns y v (ntEven (m + 2))) := ntEqvGen_ins y v hρμ
    have hEven0 : ntEven (m + 2) = ntIns 0 (0 : Fin (m + 2)) 1 := by
      have e : ntIns (0 : Fin (m + 2)) 0 (1 : Equiv.Perm (Fin (m + 1))) = 1 :=
        ntIns_zero_one
      rw [e]
      rfl
    rw [hEven0, ntIns_comm_zero y v 1 y' v' hy hv] at hcongr
    have hinnerG : ntIns y' v' (1 : Equiv.Perm (Fin (m + 1))) ∈ ntG (m + 1) :=
      ntG_id_ins hm y' v' hne'
    rcases hIH _ hinnerG with hI | hI
    · exact ntIns_close_even hcongr hI
    · exact ntIns_close_odd hcongr hI
  · have hμ'oddG : ntIns (0 : Fin (m + 2)) 0
        (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) ∈
        ntG (m + 1) := by
      have h01 : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
        intro hcon
        have hvv := congrArg Fin.val hcon
        simp only [Fin.val_zero, Fin.val_last] at hvv
        omega
      have hne0 : ((0 : Fin (m + 2)) ≠ 0 ∨ (0 : Fin (m + 2)) ≠ Fin.last (m + 1)) ∧
          ((0 : Fin (m + 2)) ≠ Fin.last (m + 1) ∨ (0 : Fin (m + 2)) ≠ 0) :=
        ⟨Or.inr h01, Or.inl h01⟩
      exact ntG_swap23_ins hm 0 0 _ rfl hne0
    have hsign' : Equiv.Perm.sign (ntIns (0 : Fin (m + 2)) 0
        (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩)) = -1 := by
      have e : ntIns (0 : Fin (m + 2)) 0
          (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) =
          Equiv.swap (⟨3, by omega⟩ : Fin (m + 2)) ⟨4, by omega⟩ := by
        rw [ntIns_zero_swap]
        congr 1
      rw [e]
      apply Equiv.Perm.sign_swap
      intro hcon
      have e2 : (3 : ℕ) = 4 := congrArg Fin.val hcon
      omega
    have hρo_sign : Equiv.Perm.sign ρ = -1 := by
      have e1 := ntEqvGen_sign hρo
      have e2 : Equiv.Perm.sign (ntOdd m) = -1 := by
        unfold ntOdd
        apply Equiv.Perm.sign_swap
        intro hcon
        have e3 : m = m + 1 := congrArg Fin.val hcon
        omega
      rw [e2] at e1
      exact e1
    have hρμ := ntG_sameSign hIH hρ hμ'oddG (hρo_sign.trans hsign'.symm)
    have hcongr := ntEqvGen_ins y v hρμ
    rw [ntIns_comm_zero y v _ y' v' hy hv] at hcongr
    have hinnerG := ntG_swap23_ins hm y' v' _ rfl hne'
    rcases hIH _ hinnerG with hI | hI
    · exact ntIns_close_even hcongr hI
    · exact ntIns_close_odd hcongr hI

/-- Closing a `last`-insertion chain at the odd reference (extra step). -/
lemma ntIns_closeLast_odd {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {w : Equiv.Perm (Fin (m + 3))}
    (hcongr : Relation.EqvGen (ntMove (m + 3)) w
      (ntIns (Fin.last (m + 2)) (Fin.last (m + 2)) (ntOdd m))) :
    Relation.EqvGen (ntMove (m + 3)) w (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3)) w (ntOdd (m + 1)) := by
  have e1 : ntOdd m =
      Equiv.swap (⟨m, by omega⟩ : Fin (m + 2)) ⟨m + 1, by omega⟩ := rfl
  have hS : ntIns (Fin.last (m + 2)) (Fin.last (m + 2)) (ntOdd m) =
      Equiv.swap ((⟨m, by omega⟩ : Fin (m + 2))).castSucc
        ((⟨m + 1, by omega⟩ : Fin (m + 2))).castSucc := by
    rw [e1]
    exact ntIns_last_swap _ _
  have h01 : (0 : Fin (m + 3)) ≠ Fin.last (m + 2) := by
    intro hcon
    have hvv := congrArg Fin.val hcon
    simp only [Fin.val_zero, Fin.val_last] at hvv
    omega
  have hS0 : ntIns (Fin.last (m + 2)) (Fin.last (m + 2)) (ntOdd m) 0 = 0 := by
    rw [hS]
    exact ntSwap_fix_vals _ _ _
      (by change (0 : ℕ) ≠ m; omega) (by change (0 : ℕ) ≠ m + 1; omega)
  obtain ⟨s', hs'⟩ := ntIns_exists _ _ _ hS0
  have hs'swap : s' =
      Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩ := by
    apply ntIns_injective (0 : Fin (m + 3)) (0 : Fin (m + 3))
    rw [← hs', hS]
    apply Equiv.Perm.ext
    intro x
    by_cases hx0 : x = 0
    · subst hx0
      rw [ntIns_apply_same]
      exact ntSwap_fix_vals _ _ _
        (by change (0 : ℕ) ≠ m; omega) (by change (0 : ℕ) ≠ m + 1; omega)
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hx0
      rw [← hi, ntIns_apply_succAbove, Fin.succAbove_zero_apply,
        Fin.succAbove_zero_apply]
      by_cases hA : i.succ = ((⟨m, by omega⟩ : Fin (m + 2))).castSucc
      · have hvv := congrArg Fin.val hA
        rw [Fin.val_succ] at hvv
        have hiv : i.val + 1 = m := hvv
        have hi_eq : i = (⟨m - 1, by omega⟩ : Fin (m + 2)) :=
          Fin.ext (by change i.val = m - 1; omega)
        rw [hA, Equiv.swap_apply_left, hi_eq, Equiv.swap_apply_left]
        rfl
      · by_cases hB : i.succ = ((⟨m + 1, by omega⟩ : Fin (m + 2))).castSucc
        · have hvv := congrArg Fin.val hB
          rw [Fin.val_succ] at hvv
          have hiv : i.val + 1 = m + 1 := hvv
          have hi_eq : i = (⟨m, by omega⟩ : Fin (m + 2)) :=
            Fin.ext (by change i.val = m; omega)
          rw [hB, Equiv.swap_apply_right, hi_eq, Equiv.swap_apply_right]
          apply Fin.ext
          rw [Fin.val_castSucc, Fin.val_succ]
          change m = m - 1 + 1
          omega
        · have eL : Equiv.swap _ _ (i.succ) = i.succ :=
            Equiv.swap_apply_of_ne_of_ne hA hB
          have eR :
              (Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩)
                i = i := by
            apply ntSwap_fix_vals
            · intro hcon
              have hiv : i.val = m - 1 := hcon
              have hAs : i.succ =
                  ((⟨m, by omega⟩ : Fin (m + 2))).castSucc := by
                apply Fin.ext
                rw [Fin.val_succ]
                change i.val + 1 = m
                omega
              exact hA hAs
            · intro hcon
              have hiv : i.val = m := hcon
              have hBs : i.succ =
                  ((⟨m + 1, by omega⟩ : Fin (m + 2))).castSucc := by
                apply Fin.ext
                rw [Fin.val_succ]
                change i.val + 1 = m + 1
                omega
              exact hB hBs
          rw [eL, eR]
  have hs'G : s' ∈ ntG (m + 1) := by
    rw [hs'swap]
    have hE : Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩ ∈
        ntE (m + 1) := by
      constructor
      · have e0 : Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩
            0 = 0 :=
          ntSwap_fix_vals _ _ _
            (by change (0 : ℕ) ≠ m - 1; omega) (by change (0 : ℕ) ≠ m; omega)
        rw [e0]
        intro hcon
        have hvv := congrArg Fin.val hcon
        simp only [Fin.val_zero, Fin.val_last] at hvv
        omega
      · have eL : Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩
            (Fin.last (m + 1)) = Fin.last (m + 1) := by
          apply ntSwap_fix_vals
          · change ((Fin.last (m + 1) : Fin (m + 2))).val ≠ m - 1
            rw [Fin.val_last]; omega
          · change ((Fin.last (m + 1) : Fin (m + 2))).val ≠ m
            rw [Fin.val_last]; omega
        rw [eL]
        intro hcon
        have hvv := congrArg Fin.val hcon
        simp only [Fin.val_zero, Fin.val_last] at hvv
        omega
    have hinc : ntInc5 (m + 2)
        (Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩) := by
      have hfix : ∀ x : Fin (m + 2), x.val ≤ 3 →
          (Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩) x = x := by
        intro x hx
        apply ntSwap_fix_vals
        · change x.val ≠ m - 1; omega
        · change x.val ≠ m; omega
      refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
        ⟨m, by omega⟩, by simp, by simp, by simp, (by change 3 < m; omega),
        ?_, ?_, ?_, ?_⟩
      · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
      · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
      · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
      · rw [hfix _ (by simp), Equiv.swap_apply_right]
        change 3 < m - 1
        omega
    exact ntMemG_of_inc5 hm hE hinc
  have hs'sign : Equiv.Perm.sign s' = -1 := by
    rw [hs'swap]
    apply Equiv.Perm.sign_swap
    intro hcon
    have e2 : m - 1 = m := congrArg Fin.val hcon
    omega
  have ht'G : ntOdd m ∈ ntG (m + 1) := ntOdd_memG hm
  have ht'sign : Equiv.Perm.sign (ntOdd m) = -1 := by
    unfold ntOdd
    apply Equiv.Perm.sign_swap
    intro hcon
    have e3 : m = m + 1 := congrArg Fin.val hcon
    omega
  have hst := ntG_sameSign hIH hs'G ht'G (hs'sign.trans ht'sign.symm)
  have hlift := ntEqvGen_ins (0 : Fin (m + 3)) (0 : Fin (m + 3)) hst
  rw [← hs', ntOdd_zero_ins] at hlift
  exact Or.inr (Relation.EqvGen.trans _ _ _ hcongr hlift)

/-- Branch 2: insertions below `last` land in a reference class. -/
lemma ntIns_branch2 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {y v : Fin (m + 3)} {ρ : Equiv.Perm (Fin (m + 2))}
    (hρ : ρ ∈ ntG (m + 1))
    (hy1 : y.val ≤ m + 1) (hv1 : v.val ≤ m + 1)
    (hne1 : (y.val, v.val) ≠ (0, m + 1)) (hne2 : (y.val, v.val) ≠ (m + 1, 0)) :
    Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntOdd (m + 1)) := by
  have hy'lt : y.val < m + 3 := y.is_lt
  have hv'lt : v.val < m + 3 := v.is_lt
  set y' : Fin (m + 2) := ⟨y.val, by omega⟩ with hy'def
  set v' : Fin (m + 2) := ⟨v.val, by omega⟩ with hv'def
  have ey : y'.val = y.val := rfl
  have ev : v'.val = v.val := rfl
  have hy : y = y'.castSucc := by
    apply Fin.ext
    rw [Fin.val_castSucc]
  have hv : v = v'.castSucc := by
    apply Fin.ext
    rw [Fin.val_castSucc]
  have hne' : (y' ≠ 0 ∨ v' ≠ Fin.last (m + 1)) ∧
      (y' ≠ Fin.last (m + 1) ∨ v' ≠ 0) := by
    constructor
    · by_contra hc
      simp only [not_or, not_not] at hc
      obtain ⟨hy0, hv0⟩ := hc
      have h1 : y'.val = 0 := by rw [hy0]; exact Fin.val_zero _
      have h2 : v'.val = m + 1 := by rw [hv0]; exact Fin.val_last _
      have hyv : y.val = 0 := by omega
      have hvv : v.val = m + 1 := by omega
      exact hne1 (by rw [hyv, hvv])
    · by_contra hc
      simp only [not_or, not_not] at hc
      obtain ⟨hy0, hv0⟩ := hc
      have h1 : y'.val = m + 1 := by rw [hy0]; exact Fin.val_last _
      have h2 : v'.val = 0 := by rw [hv0]; exact Fin.val_zero _
      have hyv : y.val = m + 1 := by omega
      have hvv : v.val = 0 := by omega
      exact hne2 (by rw [hyv, hvv])
  rcases hIH ρ hρ with hρe | hρo
  · have hμ'G : ntEven (m + 2) ∈ ntG (m + 1) := ntEven_memG hm
    have hρμ : Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) :=
      ntG_sameSign hIH hρ hμ'G (ntEqvGen_sign hρe)
    have hcongr : Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ)
        (ntIns y v (ntEven (m + 2))) := ntEqvGen_ins y v hρμ
    have hEvenL : ntEven (m + 2) =
        ntIns (Fin.last (m + 1)) (Fin.last (m + 1)) 1 := by
      have e : ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
          (1 : Equiv.Perm (Fin (m + 1))) = 1 := ntIns_last_one
      rw [e]
      rfl
    rw [hEvenL, ntIns_comm_last y v 1 y' v' hy hv] at hcongr
    have hinnerG : ntIns y' v' (1 : Equiv.Perm (Fin (m + 1))) ∈ ntG (m + 1) :=
      ntG_id_ins hm y' v' hne'
    rcases hIH _ hinnerG with hI | hI
    · exact ntIns_closeLast_even hcongr hI
    · have hstep := ntEqvGen_ins (Fin.last (m + 2)) (Fin.last (m + 2)) hI
      exact ntIns_closeLast_odd hm hIH
        (Relation.EqvGen.trans _ _ _ hcongr hstep)
  · have hμ'oddG : ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
        (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) ∈
        ntG (m + 1) := by
      have hE : ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
          (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) ∈
          ntE (m + 1) := by
        have h01 : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
          intro hcon
          have hvv := congrArg Fin.val hcon
          simp only [Fin.val_zero, Fin.val_last] at hvv
          omega
        constructor
        · intro hcon
          obtain ⟨i, hi⟩ :=
            Fin.exists_succAbove_eq (show (0 : Fin (m + 2)) ≠
              Fin.last (m + 1) from h01)
          have hi00 : i = 0 := by
            have e := congrArg Fin.val hi
            rw [Fin.succAbove_last_apply] at e
            rw [Fin.val_castSucc] at e
            have e2 : i.val = 0 := by simpa using e
            exact Fin.ext e2
          subst hi00
          have e2 : ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
              (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) 0 =
              ((0 : Fin (m + 1))).castSucc := by
            rw [← hi, ntIns_apply_succAbove,
              ntSwap_fix_vals _ _ _ (by simp) (by simp),
              Fin.succAbove_last_apply]
          rw [e2] at hcon
          have hvv := congrArg Fin.val hcon
          simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last] at hvv
          omega
        · rw [ntIns_apply_same]
          intro hcon
          have hvv := congrArg Fin.val hcon
          simp only [Fin.val_zero, Fin.val_last] at hvv
          omega
      have hinc : ntInc5 (m + 2) (ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
          (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩)) :=
        ntInc5_swap23_ins hm _ _ _ rfl
      exact ntMemG_of_inc5 hm hE hinc
    have hsign' : Equiv.Perm.sign (ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
        (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩)) = -1 := by
      have e : ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
          (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) =
          Equiv.swap ((⟨2, by omega⟩ : Fin (m + 1))).castSucc
            ((⟨3, by omega⟩ : Fin (m + 1))).castSucc := by
        exact ntIns_last_swap _ _
      rw [e]
      apply Equiv.Perm.sign_swap
      intro hcon
      have e2 : (2 : ℕ) = 3 := congrArg Fin.val hcon
      omega
    have hρo_sign : Equiv.Perm.sign ρ = -1 := by
      have e1 := ntEqvGen_sign hρo
      have e2 : Equiv.Perm.sign (ntOdd m) = -1 := by
        unfold ntOdd
        apply Equiv.Perm.sign_swap
        intro hcon
        have e3 : m = m + 1 := congrArg Fin.val hcon
        omega
      rw [e2] at e1
      exact e1
    have hρμ := ntG_sameSign hIH hρ hμ'oddG (hρo_sign.trans hsign'.symm)
    have hcongr := ntEqvGen_ins y v hρμ
    rw [ntIns_comm_last y v _ y' v' hy hv] at hcongr
    have hinnerG := ntG_swap23_ins hm y' v' _ rfl hne'
    rcases hIH _ hinnerG with hI | hI
    · exact ntIns_closeLast_even hcongr hI
    · have hstep := ntEqvGen_ins (Fin.last (m + 2)) (Fin.last (m + 2)) hI
      exact ntIns_closeLast_odd hm hIH
        (Relation.EqvGen.trans _ _ _ hcongr hstep)

/-- The `0-1` swap is generic (used for odd witness move results). -/
lemma ntSwap01_memG {m : ℕ} (hm : 5 ≤ m) :
    Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
      (⟨1, by omega⟩ : Fin (m + 2)) ∈ ntG (m + 1) := by
  have hE : Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
      (⟨1, by omega⟩ : Fin (m + 2)) ∈ ntE (m + 1) := by
    constructor
    · have e0 : Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
          (⟨1, by omega⟩ : Fin (m + 2)) 0 =
          (⟨1, by omega⟩ : Fin (m + 2)) :=
        Equiv.swap_apply_left _ _
      rw [e0]
      intro hcon
      have hvv := congrArg Fin.val hcon
      simp only [Fin.val_last] at hvv
      omega
    · have eL : Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
          (⟨1, by omega⟩ : Fin (m + 2)) (Fin.last (m + 1)) =
          Fin.last (m + 1) := by
        apply ntSwap_fix_vals
        · change ((Fin.last (m + 1) : Fin (m + 2))).val ≠ 0
          rw [Fin.val_last]; omega
        · change ((Fin.last (m + 1) : Fin (m + 2))).val ≠ 1
          rw [Fin.val_last]; omega
      rw [eL]
      intro hcon
      have hvv := congrArg Fin.val hcon
      simp only [Fin.val_zero, Fin.val_last] at hvv
      omega
  have hinc : ntInc5 (m + 2) (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
      (⟨1, by omega⟩ : Fin (m + 2))) := by
    have hfix : ∀ x : Fin (m + 2), 2 ≤ x.val →
        (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
          (⟨1, by omega⟩ : Fin (m + 2))) x = x := by
      intro x hx
      apply ntSwap_fix_vals
      · change x.val ≠ 0; omega
      · change x.val ≠ 1; omega
    refine ⟨⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩,
      ⟨6, by omega⟩, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
  exact ntMemG_of_inc5 hm hE hinc

/-- Even inner permutation for the `(1, n-1)` witness. -/
lemma ntMuP1e {m : ℕ} (hm : 5 ≤ m) :
    ∃ μe : Equiv.Perm (Fin (m + 2)),
      μe (⟨0, by omega⟩ : Fin (m + 2)) = (⟨2, by omega⟩ : Fin (m + 2)) ∧
      μe (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)) ∧
      μe (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)) ∧
      μe ∈ ntG (m + 1) ∧ Equiv.Perm.sign μe = 1 ∧
      ∀ x : Fin (m + 2), 3 ≤ x.val → μe x = x := by
  have d01 : (⟨0, by omega⟩ : Fin (m + 2)) ≠ (⟨1, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have d02 : (⟨0, by omega⟩ : Fin (m + 2)) ≠ (⟨2, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have d10 : (⟨1, by omega⟩ : Fin (m + 2)) ≠ (⟨0, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have d12 : (⟨1, by omega⟩ : Fin (m + 2)) ≠ (⟨2, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have d20 : (⟨2, by omega⟩ : Fin (m + 2)) ≠ (⟨0, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have d21 : (⟨2, by omega⟩ : Fin (m + 2)) ≠ (⟨1, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have dL0 : (Fin.last (m + 1) : Fin (m + 2)) ≠ (⟨0, by omega⟩ : Fin (m + 2)) := by
    intro hcon
    have hv := congrArg Fin.val hcon
    simp only [Fin.val_last] at hv
    omega
  have dL1 : (Fin.last (m + 1) : Fin (m + 2)) ≠ (⟨1, by omega⟩ : Fin (m + 2)) := by
    intro hcon
    have hv := congrArg Fin.val hcon
    simp only [Fin.val_last] at hv
    omega
  have dL2 : (Fin.last (m + 1) : Fin (m + 2)) ≠ (⟨2, by omega⟩ : Fin (m + 2)) := by
    intro hcon
    have hv := congrArg Fin.val hcon
    simp only [Fin.val_last] at hv
    omega
  have z0 : (0 : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)) := rfl
  have hfix : ∀ x : Fin (m + 2), 3 ≤ x.val →
      (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨1, by omega⟩ : Fin (m + 2)) *
      Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨2, by omega⟩ : Fin (m + 2))) x = x := by
    intro x hx
    rw [Equiv.Perm.mul_apply]
    have e2 : Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨2, by omega⟩ : Fin (m + 2)) x = x := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro hcon
        have hv : x.val = 0 := congrArg Fin.val hcon
        omega
      · intro hcon
        have hv : x.val = 2 := congrArg Fin.val hcon
        omega
    have e1 : Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨1, by omega⟩ : Fin (m + 2)) x = x := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro hcon
        have hv : x.val = 0 := congrArg Fin.val hcon
        omega
      · intro hcon
        have hv : x.val = 1 := congrArg Fin.val hcon
        omega
    rw [e2, e1]
  refine ⟨Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
      (⟨1, by omega⟩ : Fin (m + 2)) *
    Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
      (⟨2, by omega⟩ : Fin (m + 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne d20 d21]
  · rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne d10 d12, Equiv.swap_apply_right]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  · have hE : (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨1, by omega⟩ : Fin (m + 2)) *
      Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨2, by omega⟩ : Fin (m + 2))) ∈ ntE (m + 1) := by
      constructor
      · rw [z0, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne d20 d21]
        intro hcon
        have hvv := congrArg Fin.val hcon
        simp only [Fin.val_last] at hvv
        omega
      · have eL : (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
            (⟨1, by omega⟩ : Fin (m + 2)) *
          Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
            (⟨2, by omega⟩ : Fin (m + 2))) (Fin.last (m + 1)) =
            Fin.last (m + 1) := by
          rw [Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne dL0 dL2,
            Equiv.swap_apply_of_ne_of_ne dL0 dL1]
        rw [eL]
        intro hcon
        have hvv := congrArg Fin.val hcon
        simp only [Fin.val_zero, Fin.val_last] at hvv
        omega
    have hinc : ntInc5 (m + 2) (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨1, by omega⟩ : Fin (m + 2)) *
        Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
          (⟨2, by omega⟩ : Fin (m + 2))) := by
      refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩,
        ⟨5, by omega⟩, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne d10 d12,
          Equiv.swap_apply_right, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
          Equiv.swap_apply_left]
        simp
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left,
          hfix _ (by simp)]
        change (1 : ℕ) < 3
        omega
      · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
      · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    exact ntMemG_of_inc5 hm hE hinc
  · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap d01, Equiv.Perm.sign_swap d02]
    decide
  · exact hfix

/-- Odd inner permutation for the `(1, n-1)` witness. -/
lemma ntMuP1o {m : ℕ} (hm : 5 ≤ m)
    {μe : Equiv.Perm (Fin (m + 2))}
    (f0 : μe (⟨0, by omega⟩ : Fin (m + 2)) = (⟨2, by omega⟩ : Fin (m + 2)))
    (f1 : μe (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)))
    (f2 : μe (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)))
    (hse : Equiv.Perm.sign μe = 1)
    (hfix : ∀ x : Fin (m + 2), 3 ≤ x.val → μe x = x) :
    let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
      (⟨m + 1, by omega⟩ : Fin (m + 2))
    μo ∈ ntG (m + 1) ∧ Equiv.Perm.sign μo = -1 := by
  dsimp only
  have dM : (⟨m, by omega⟩ : Fin (m + 2)) ≠
      (⟨m + 1, by omega⟩ : Fin (m + 2)) := by
    intro h
    have := congrArg Fin.val h
    change m = m + 1 at this
    omega
  have Sfix : ∀ x : Fin (m + 2), x.val ≠ m → x.val ≠ m + 1 →
      Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
        (⟨m + 1, by omega⟩ : Fin (m + 2)) x = x := by
    intro x hxm hxm1
    apply ntSwap_fix_vals
    · exact hxm
    · exact hxm1
  constructor
  · apply ntMemG_of_inc5 hm
    · constructor
      · rw [Equiv.Perm.mul_apply,
          Sfix _ (by change 0 ≠ m; omega) (by change 0 ≠ m + 1; omega)]
        change μe (⟨0, by omega⟩ : Fin (m + 2)) ≠ Fin.last (m + 1)
        rw [f0]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last] at this
        omega
      · have hlast : (Fin.last (m + 1) : Fin (m + 2)) =
            (⟨m + 1, by omega⟩ : Fin (m + 2)) := Fin.ext (Fin.val_last _)
        rw [Equiv.Perm.mul_apply, hlast, Equiv.swap_apply_right,
          hfix _ (show (3 : ℕ) ≤ m from by omega)]
        intro h
        have := congrArg Fin.val h
        change m = 0 at this
        omega
    · have g1 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
            (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨1, by omega⟩ : Fin (m + 2)) =
          (⟨0, by omega⟩ : Fin (m + 2)) := by
        rw [Equiv.Perm.mul_apply,
          Sfix _ (by change 1 ≠ m; omega) (by change 1 ≠ m + 1; omega), f1]
      have g2 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
            (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨2, by omega⟩ : Fin (m + 2)) =
          (⟨1, by omega⟩ : Fin (m + 2)) := by
        rw [Equiv.Perm.mul_apply,
          Sfix _ (by change 2 ≠ m; omega) (by change 2 ≠ m + 1; omega), f2]
      have g3 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
            (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨3, by omega⟩ : Fin (m + 2)) =
          (⟨3, by omega⟩ : Fin (m + 2)) := by
        rw [Equiv.Perm.mul_apply, Sfix _ (by change 3 ≠ m; omega)
          (by change 3 ≠ m + 1; omega), hfix _ (by norm_num)]
      have g4 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
            (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨4, by omega⟩ : Fin (m + 2)) =
          (⟨4, by omega⟩ : Fin (m + 2)) := by
        rw [Equiv.Perm.mul_apply, Sfix _ (by change 4 ≠ m; omega)
          (by change 4 ≠ m + 1; omega), hfix _ (by norm_num)]
      have gm : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
            (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨m, by omega⟩ : Fin (m + 2)) =
          (⟨m + 1, by omega⟩ : Fin (m + 2)) := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          hfix _ (show (3 : ℕ) ≤ m + 1 from by omega)]
      refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩,
        ⟨m, by omega⟩, by simp, by simp, by simp, (by change 4 < m; omega),
        ?_, ?_, ?_, ?_⟩
      · rw [g1, g2, Fin.lt_def]
        simp
      · rw [g2, g3]
        change (1 : ℕ) < 3
        omega
      · rw [g3, g4, Fin.lt_def]
        simp
      · rw [g4, gm]
        change 4 < m + 1
        omega
  · rw [Equiv.Perm.sign_mul, hse, Equiv.Perm.sign_swap dM]
    simp

lemma ntG_symm_of_inc5 {m : ℕ} (hm : 5 ≤ m)
    {σ : Equiv.Perm (Fin (m + 2))} (hG : σ ∈ ntG (m + 1))
    (hinc : ntInc5 (m + 2) σ) : σ.symm ∈ ntG (m + 1) :=
  ntMemG_of_inc5 hm (ntE_symm hG.1) (ntInc5_symm hinc)

lemma ntG_rc_of_inc5 {m : ℕ} (hm : 5 ≤ m)
    {σ : Equiv.Perm (Fin (m + 2))} (hG : σ ∈ ntG (m + 1))
    (hinc : ntInc5 (m + 2) σ) : ntRC σ ∈ ntG (m + 1) :=
  ntMemG_of_inc5 hm (ntE_rc hG.1) (ntInc5_rc hinc)

lemma ntG_rc_symm_of_inc5 {m : ℕ} (hm : 5 ≤ m)
    {σ : Equiv.Perm (Fin (m + 2))} (hG : σ ∈ ntG (m + 1))
    (hinc : ntInc5 (m + 2) σ) : ntRC σ.symm ∈ ntG (m + 1) :=
  ntG_rc_of_inc5 hm (ntG_symm_of_inc5 hm hG hinc) (ntInc5_symm hinc)

lemma ntInsertion_pair1 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {ρ : Equiv.Perm (Fin (m + 2))} (hρ : ρ ∈ ntG (m + 1)) :
    Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨1, by omega⟩ : Fin (m + 3)) (⟨m + 2, by omega⟩ : Fin (m + 3)) ρ)
        (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨1, by omega⟩ : Fin (m + 3)) (⟨m + 2, by omega⟩ : Fin (m + 3)) ρ)
        (ntOdd (m + 1)) := by
  obtain ⟨μe, f0, f1, f2, hμe, hse, hfix⟩ := ntMuP1e hm
  let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))
  have hμo : μo ∈ ntG (m + 1) := (ntMuP1o hm f0 f1 f2 hse hfix).1
  have hso : Equiv.Perm.sign μo = -1 := (ntMuP1o hm f0 f1 f2 hse hfix).2
  have hste := ntPair1e_step hm
    (y := (⟨1, by omega⟩ : Fin (m + 3)))
    (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix
  have hsto := ntPair1o_step hm
    (y := (⟨1, by omega⟩ : Fin (m + 3)))
    (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix
  have hce := ntIns_branch1 hm hIH (y := (⟨3, by omega⟩ : Fin (m + 3)))
    (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) (hρ := ntEven_memG hm)
    (by norm_num) (by change 1 ≤ m + 2; omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      simp at h')
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
  have hco := ntIns_branch1 hm hIH (y := (⟨3, by omega⟩ : Fin (m + 3)))
    (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) (hρ := ntOdd_memG hm)
    (by norm_num) (by change 1 ≤ m + 2; omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      simp at h')
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
  exact ntIns_parity_transfer hIH hρ hμe hse hμo hso hste hsto hce hco

lemma ntInsertion_pair3 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {ρ : Equiv.Perm (Fin (m + 2))} (hρ : ρ ∈ ntG (m + 1)) :
    Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨1, by omega⟩ : Fin (m + 3)) ρ)
        (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨1, by omega⟩ : Fin (m + 3)) ρ)
        (ntOdd (m + 1)) := by
  obtain ⟨μe, f0, f1, f2, hμe, hse, hfix⟩ := ntMuP1e hm
  let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))
  have hμo : μo ∈ ntG (m + 1) := (ntMuP1o hm f0 f1 f2 hse hfix).1
  have hso : Equiv.Perm.sign μo = -1 := (ntMuP1o hm f0 f1 f2 hse hfix).2
  have hince := ntMuP1e_inc hm f1 f2 hfix
  have hinco := ntMuP1o_inc hm f1 f2 hfix
  have hμes : μe.symm ∈ ntG (m + 1) := ntG_symm_of_inc5 hm hμe hince
  have hμos : μo.symm ∈ ntG (m + 1) := ntG_symm_of_inc5 hm hμo hinco
  have hses : Equiv.Perm.sign μe.symm = 1 := by
    rw [Equiv.Perm.sign_symm, hse]
  have hsos : Equiv.Perm.sign μo.symm = -1 := by
    rw [Equiv.Perm.sign_symm, hso]
  have hste : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨1, by omega⟩ : Fin (m + 3)) μe.symm)
      (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3)) 1) := by
    have h := ntEqvGen_symm (ntPair1e_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    have hone : (1 : Equiv.Perm (Fin (m + 2))).symm = 1 := rfl
    simpa only [ntIns_symm, hone] using h
  have hsto : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨1, by omega⟩ : Fin (m + 3)) μo.symm)
      (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3))
        (ntOdd m)) := by
    have h := ntEqvGen_symm (ntPair1o_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    simpa only [ntIns_symm, ntOdd_symm] using h
  have hce := ntIns_branch1 hm hIH (y := (⟨m + 2, by omega⟩ : Fin (m + 3)))
    (v := (⟨3, by omega⟩ : Fin (m + 3))) (hρ := ntEven_memG hm)
    (by change 1 ≤ m + 2; omega) (by norm_num)
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.snd h
      simp at h')
  have hco := ntIns_branch1 hm hIH (y := (⟨m + 2, by omega⟩ : Fin (m + 3)))
    (v := (⟨3, by omega⟩ : Fin (m + 3))) (hρ := ntOdd_memG hm)
    (by change 1 ≤ m + 2; omega) (by norm_num)
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.snd h
      simp at h')
  exact ntIns_parity_transfer hIH hρ hμes hses hμos hsos hste hsto hce hco

lemma ntInsertion_pair2 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {ρ : Equiv.Perm (Fin (m + 2))} (hρ : ρ ∈ ntG (m + 1)) :
    Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨m + 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3)) ρ)
        (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨m + 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3)) ρ)
        (ntOdd (m + 1)) := by
  obtain ⟨μe, f0, f1, f2, hμe, hse, hfix⟩ := ntMuP1e hm
  let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))
  have hμo : μo ∈ ntG (m + 1) := (ntMuP1o hm f0 f1 f2 hse hfix).1
  have hso : Equiv.Perm.sign μo = -1 := (ntMuP1o hm f0 f1 f2 hse hfix).2
  have hince := ntMuP1e_inc hm f1 f2 hfix
  have hinco := ntMuP1o_inc hm f1 f2 hfix
  have hμer : ntRC μe ∈ ntG (m + 1) := ntG_rc_of_inc5 hm hμe hince
  have hμor : ntRC μo ∈ ntG (m + 1) := ntG_rc_of_inc5 hm hμo hinco
  have hser : Equiv.Perm.sign (ntRC μe) = 1 := by rw [ntRC_sign, hse]
  have hsor : Equiv.Perm.sign (ntRC μo) = -1 := by rw [ntRC_sign, hso]
  have hr1 : (⟨1, by omega⟩ : Fin (m + 3)).rev =
      (⟨m + 1, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hr3 : (⟨3, by omega⟩ : Fin (m + 3)).rev =
      (⟨m - 1, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hrL : (⟨m + 2, by omega⟩ : Fin (m + 3)).rev =
      (⟨0, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hste : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨m + 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3)) (ntRC μe))
      (ntIns (⟨m - 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3)) 1) := by
    have h := ntEqvGen_rc (ntPair1e_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    rw [ntRC_ins, ntRC_ins, hr1, hr3, hrL, ntRC_one] at h
    exact h
  have hsto : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨m + 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3)) (ntRC μo))
      (ntIns (⟨m - 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3))
        (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2)) ⟨1, by omega⟩)) := by
    have h := ntEqvGen_rc (ntPair1o_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    rw [ntRC_ins, ntRC_ins, hr1, hr3, hrL, ntRC_odd] at h
    exact h
  have hce := ntIns_branch2 hm hIH (y := (⟨m - 1, by omega⟩ : Fin (m + 3)))
    (v := (⟨0, by omega⟩ : Fin (m + 3))) (hρ := ntEven_memG hm)
    (by change m - 1 ≤ m + 1; omega) (by norm_num)
    (by
      intro h
      have h' := congrArg Prod.snd h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
  have hco := ntIns_branch2 hm hIH (y := (⟨m - 1, by omega⟩ : Fin (m + 3)))
    (v := (⟨0, by omega⟩ : Fin (m + 3))) (hρ := ntSwap01_memG hm)
    (by change m - 1 ≤ m + 1; omega) (by norm_num)
    (by
      intro h
      have h' := congrArg Prod.snd h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
  exact ntIns_parity_transfer hIH hρ hμer hser hμor hsor hste hsto hce hco

lemma ntInsertion_pair4 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {ρ : Equiv.Perm (Fin (m + 2))} (hρ : ρ ∈ ntG (m + 1)) :
    Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m + 1, by omega⟩ : Fin (m + 3)) ρ)
        (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m + 1, by omega⟩ : Fin (m + 3)) ρ)
        (ntOdd (m + 1)) := by
  obtain ⟨μe, f0, f1, f2, hμe, hse, hfix⟩ := ntMuP1e hm
  let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))
  have hμo : μo ∈ ntG (m + 1) := (ntMuP1o hm f0 f1 f2 hse hfix).1
  have hso : Equiv.Perm.sign μo = -1 := (ntMuP1o hm f0 f1 f2 hse hfix).2
  have hince := ntMuP1e_inc hm f1 f2 hfix
  have hinco := ntMuP1o_inc hm f1 f2 hfix
  have hμers : ntRC μe.symm ∈ ntG (m + 1) := ntG_rc_symm_of_inc5 hm hμe hince
  have hμors : ntRC μo.symm ∈ ntG (m + 1) := ntG_rc_symm_of_inc5 hm hμo hinco
  have hsers : Equiv.Perm.sign (ntRC μe.symm) = 1 := by
    rw [ntRC_sign, Equiv.Perm.sign_symm, hse]
  have hsors : Equiv.Perm.sign (ntRC μo.symm) = -1 := by
    rw [ntRC_sign, Equiv.Perm.sign_symm, hso]
  have hr1 : (⟨1, by omega⟩ : Fin (m + 3)).rev =
      (⟨m + 1, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hr3 : (⟨3, by omega⟩ : Fin (m + 3)).rev =
      (⟨m - 1, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hrL : (⟨m + 2, by omega⟩ : Fin (m + 3)).rev =
      (⟨0, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hste : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m + 1, by omega⟩ : Fin (m + 3))
        (ntRC μe.symm))
      (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m - 1, by omega⟩ : Fin (m + 3)) 1) := by
    have h := ntEqvGen_symm (ntPair1e_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    have hone : (1 : Equiv.Perm (Fin (m + 2))).symm = 1 := rfl
    rw [ntIns_symm, ntIns_symm, hone] at h
    have h := ntEqvGen_rc h
    rw [ntRC_ins, ntRC_ins, hr1, hr3, hrL, ntRC_one] at h
    exact h
  have hsto : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m + 1, by omega⟩ : Fin (m + 3))
        (ntRC μo.symm))
      (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m - 1, by omega⟩ : Fin (m + 3))
        (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2)) ⟨1, by omega⟩)) := by
    have h := ntEqvGen_symm (ntPair1o_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    rw [ntIns_symm, ntIns_symm, ntOdd_symm] at h
    have h := ntEqvGen_rc h
    rw [ntRC_ins, ntRC_ins, hr1, hr3, hrL, ntRC_odd] at h
    exact h
  have hce := ntIns_branch2 hm hIH (y := (⟨0, by omega⟩ : Fin (m + 3)))
    (v := (⟨m - 1, by omega⟩ : Fin (m + 3))) (hρ := ntEven_memG hm)
    (by norm_num) (by change m - 1 ≤ m + 1; omega)
    (by
      intro h
      have h' := congrArg Prod.snd h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      simp at h')
  have hco := ntIns_branch2 hm hIH (y := (⟨0, by omega⟩ : Fin (m + 3)))
    (v := (⟨m - 1, by omega⟩ : Fin (m + 3))) (hρ := ntSwap01_memG hm)
    (by norm_num) (by change m - 1 ≤ m + 1; omega)
    (by
      intro h
      have h' := congrArg Prod.snd h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      simp at h')
  exact ntIns_parity_transfer hIH hρ hμers hsers hμors hsors hste hsto hce hco

end MetaMathlibExt
