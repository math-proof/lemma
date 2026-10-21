import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000


abbrev M2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 3)

private def m2 (a b c d : ZMod 3) : M2 := Matrix.of fun i j => if i = 0 then if j = 0 then a else b else if j = 0 then c else d

private noncomputable def X (M : M2) : M2 := m2 0 (M 0 1) (-M 1 0) 0

private lemma key
  (a b c d : ZMod 3) :
  -- imply
  ((m2 a b c d : M2) ^ 4 = -1 → X (m2 a b c d) * m2 a b c d = m2 a b c d ^ 3 * X (m2 a b c d) ∧ (X (m2 a b c d)).det ≠ 0 ∧ Matrix.trace (m2 a b c d : M2) ≠ 0) ∧ ((m2 a b c d : M2) ^ 8 = 1 → (m2 a b c d : M2) ^ 4 ≠ 1 → (m2 a b c d : M2) ^ 4 = -1) := by
  -- proof
  fin_cases a
  all_goals fin_cases b
  all_goals fin_cases c
  all_goals fin_cases d
  all_goals decide

private lemma coe_pow_four_eq_neg_one
  {g : GL (Fin 2) (ZMod 3)}
  -- given
  (hg : orderOf g = 8) :
  -- imply
  (g : M2) ^ 4 = -1 := by
  -- proof
  have h8 : (g : M2) ^ 8 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  have h4 : (g : M2) ^ 4 ≠ 1 := by
    intro h
    apply absurd (Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one]))
    apply pow_ne_one_of_lt_orderOf (by norm_num)
    rw [hg]
    norm_num
  have e : (g : M2) = m2 ((g : M2) 0 0) ((g : M2) 0 1) ((g : M2) 1 0) ((g : M2) 1 1) := Matrix.eta_fin_two _
  rw [e] at h8 h4 ⊢
  apply (key _ _ _ _).2 h8 h4

private lemma isConj_pow_three_of_orderOf_eq_eight
  {g : GL (Fin 2) (ZMod 3)}
  -- given
  (hg : orderOf g = 8) :
  -- imply
  IsConj g (g ^ 3) := by
  -- proof
  have h4 := coe_pow_four_eq_neg_one hg
  have e : (g : M2) = m2 ((g : M2) 0 0) ((g : M2) 0 1) ((g : M2) 1 0) ((g : M2) 1 1) := Matrix.eta_fin_two _
  have hpow : (m2 ((g : M2) 0 0) ((g : M2) 0 1) ((g : M2) 1 0) ((g : M2) 1 1) : M2) ^ 4 = -1 := by
    rw [← e]
    apply h4
  have hk := (key ((g : M2) 0 0) ((g : M2) 0 1) ((g : M2) 1 0) ((g : M2) 1 1)).1 hpow
  rw [← e] at hk
  obtain ⟨hXM, hdet, _⟩ := hk
  let c : GL (Fin 2) (ZMod 3) := Matrix.GeneralLinearGroup.mkOfDetNeZero (X (g : M2)) hdet
  refine (Iff.mpr isConj_iff) ⟨c, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  show X (g : M2) * (g : M2) = ((g ^ 3 : GL (Fin 2) (ZMod 3)) : M2) * X (g : M2)
  rw [Units.val_pow_eq_pow_val]
  apply hXM

private lemma not_isConj_pow_five_of_orderOf_eq_eight
  {g : GL (Fin 2) (ZMod 3)}
  -- given
  (hg : orderOf g = 8) :
  -- imply
  ¬ IsConj g (g ^ 5) := by
  -- proof
  have h4 := coe_pow_four_eq_neg_one hg
  have e : (g : M2) = m2 ((g : M2) 0 0) ((g : M2) 0 1) ((g : M2) 1 0) ((g : M2) 1 1) := Matrix.eta_fin_two _
  have hpow : (m2 ((g : M2) 0 0) ((g : M2) 0 1) ((g : M2) 1 0) ((g : M2) 1 1) : M2) ^ 4 = -1 := by
    rw [← e]
    apply h4
  have hk := (key ((g : M2) 0 0) ((g : M2) 0 1) ((g : M2) 1 0) ((g : M2) 1 1)).1 hpow
  obtain ⟨_, _, htr⟩ := hk
  rw [← e] at htr
  intro hc
  obtain ⟨c, hc⟩ := Iff.mp isConj_iff hc
  have h5 : ((g ^ 5 : GL (Fin 2) (ZMod 3)) : M2) = -(g : M2) := by
    rw [Units.val_pow_eq_pow_val, pow_succ, h4]
    simp
  have htr' : Matrix.trace (g : M2) = Matrix.trace ((g ^ 5 : GL (Fin 2) (ZMod 3)) : M2) := by
    rw [← hc]
    simp only [Units.val_mul]
    rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [h5, Matrix.trace_neg] at htr'
  apply htr
  suffices h2 : (2 : ZMod 3) * Matrix.trace (g : M2) = 0 by
    apply (Iff.mp mul_eq_zero h2).resolve_left (by decide)
  rw [two_mul]
  nth_rw 1 [htr']
  ring

private lemma card_centralizer_of_orderOf_eq_eight
  {g : GL (Fin 2) (ZMod 3)}
  -- given
  (hg : orderOf g = 8)
  (hle : Subgroup.centralizer ({g} : Set (GL (Fin 2) (ZMod 3))) ≤ Subgroup.zpowers g) :
  -- imply
  Nat.card (Subgroup.centralizer ({g} : Set (GL (Fin 2) (ZMod 3)))) = 8 := by
  -- proof
  have heq : Subgroup.centralizer ({g} : Set (GL (Fin 2) (ZMod 3))) = Subgroup.zpowers g := by
    refine le_antisymm hle ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  rw [heq, Nat.card_zpowers, hg]

/--
[GL2F3_isConj_pow_three_of_orderOf_eq_eight](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GL2F3_isConj_pow_three_of_orderOf_eq_eight.lean)
-/
@[path]
private lemma main
  {g : GL (Fin 2) (ZMod 3)}
  -- given
  (hg : orderOf g = 8) :
  -- imply
  IsConj g (g ^ 3) := by
  -- proof
  apply isConj_pow_three_of_orderOf_eq_eight hg


-- created on 2026-10-20
