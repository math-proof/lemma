import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

abbrev M2 := Matrix (Fin 2) (Fin 2) (ZMod 3)
private noncomputable def X (M : M2) : M2 := !![0, M 0 1; -M 1 0, 0]
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
private lemma key (a b c d : ZMod 3) :
    ((!![a, b; c, d] : M2) ^ 4 = -1 →
      X !![a, b; c, d] * !![a, b; c, d] = !![a, b; c, d] ^ 3 * X !![a, b; c, d] ∧
      (X !![a, b; c, d]).det ≠ 0 ∧ Matrix.trace (!![a, b; c, d] : M2) ≠ 0) ∧
    ((!![a, b; c, d] : M2) ^ 8 = 1 → (!![a, b; c, d] : M2) ^ 4 ≠ 1 → (!![a, b; c, d] : M2) ^ 4 = -1) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
private lemma coe_pow_four_eq_neg_one (g : GL (Fin 2) (ZMod 3)) (hg : orderOf g = 8) :
    ((g : M2)) ^ 4 = -1 := by
  have h8 : (g : M2) ^ 8 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  have h4 : (g : M2) ^ 4 ≠ 1 := by
    intro h
    have : g ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    exact absurd this (pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hg]; norm_num))
  have e : (g : M2) = !![(g : M2) 0 0, (g : M2) 0 1; (g : M2) 1 0, (g : M2) 1 1] := Matrix.eta_fin_two _
  rw [e] at h8 h4 ⊢
  exact (key _ _ _ _).2 h8 h4
private lemma isConj_pow_three_of_orderOf_eq_eight (g : GL (Fin 2) (ZMod 3)) (hg : orderOf g = 8) :
    IsConj g (g ^ 3) := by
  have h4 := coe_pow_four_eq_neg_one g hg
  have e : (g : M2) = !![(g : M2) 0 0, (g : M2) 0 1; (g : M2) 1 0, (g : M2) 1 1] := Matrix.eta_fin_two _
  have hk := (key ((g : M2) 0 0) ((g : M2) 0 1) ((g : M2) 1 0) ((g : M2) 1 1)).1 (by rw [← e]; exact h4)
  rw [← e] at hk
  obtain ⟨hXM, hdet, -⟩ := hk
  let c : GL (Fin 2) (ZMod 3) := Matrix.GeneralLinearGroup.mkOfDetNeZero (X (g : M2)) hdet
  refine isConj_iff.mpr ⟨c, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  show X (g : M2) * (g : M2) = ((g ^ 3 : GL (Fin 2) (ZMod 3)) : M2) * X (g : M2)
  rw [Units.val_pow_eq_pow_val]
  exact hXM
private lemma not_isConj_pow_five_of_orderOf_eq_eight (g : GL (Fin 2) (ZMod 3)) (hg : orderOf g = 8) :
    ¬ IsConj g (g ^ 5) := by
  have h4 := coe_pow_four_eq_neg_one g hg
  have e : (g : M2) = !![(g : M2) 0 0, (g : M2) 0 1; (g : M2) 1 0, (g : M2) 1 1] := Matrix.eta_fin_two _
  have hk := (key ((g : M2) 0 0) ((g : M2) 0 1) ((g : M2) 1 0) ((g : M2) 1 1)).1 (by rw [← e]; exact h4)
  obtain ⟨-, -, htr⟩ := hk
  rw [← e] at htr
  intro hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have h5 : ((g ^ 5 : GL (Fin 2) (ZMod 3)) : M2) = -(g : M2) := by
    rw [Units.val_pow_eq_pow_val, pow_succ, h4]; simp
  have htr' : Matrix.trace ((g : M2)) = Matrix.trace (((g ^ 5 : GL (Fin 2) (ZMod 3)) : M2)) := by
    rw [← hc]
    simp only [Units.val_mul]
    rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [h5, Matrix.trace_neg] at htr'
  apply htr
  have h2 : (2 : ZMod 3) * Matrix.trace (g : M2) = 0 := by rw [two_mul]; nth_rw 1 [htr']; ring
  have h2u : (2 : ZMod 3) ≠ 0 := by decide
  exact (mul_eq_zero.mp h2).resolve_left h2u
private lemma card_centralizer_of_orderOf_eq_eight (g : GL (Fin 2) (ZMod 3)) (hg : orderOf g = 8)
    (hle : Subgroup.centralizer ({g} : Set (GL (Fin 2) (ZMod 3))) ≤ Subgroup.zpowers g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL (Fin 2) (ZMod 3)))) = 8 := by
  have heq : Subgroup.centralizer ({g} : Set (GL (Fin 2) (ZMod 3))) = Subgroup.zpowers g := by
    refine le_antisymm hle ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  rw [heq, Nat.card_zpowers, hg]
/--
[GL2F3_isConj_pow_three_of_orderOf_eq_eight](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GL2F3_isConj_pow_three_of_orderOf_eq_eight.lean)
-/
@[path]
private lemma main (g : GL (Fin 2) (ZMod 3))
    (hg : orderOf g = 8) : IsConj g (g ^ 3) :=
  isConj_pow_three_of_orderOf_eq_eight g hg

-- created on 2026-10-20
