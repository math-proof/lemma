import Mathlib
import sympy.Basic

namespace AddMonoidHom

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

structure IsDualPair (φ : A →+ B) (ψ : B →+ A) (n : ℤ) : Prop where
  comp_left : ∀ a, ψ (φ a) = n • a
  comp_right : ∀ b, φ (ψ b) = n • b

theorem IsDualPair.ker_le_torsion_left {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (h : IsDualPair φ ψ n) {b : B} (hb : ψ b = 0) : n • b = 0 := by
  rw [← h.comp_right b, hb, map_zero]

end AddMonoidHom

/--
[AddMonoidHom_IsDualPair_forall_q_zsmul_eq_zero_of_isCoprime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_IsDualPair_forall_q_zsmul_eq_zero_of_isCoprime.lean)
-/
@[path]
private lemma main
  [AddCommGroup A] [AddCommGroup B]
  {φ : A →+ B}
  {ψ : B →+ A}
  {n : ℤ}
  {q : ℕ}
-- given
  (hdual : AddMonoidHom.IsDualPair φ ψ n)
  (hcop : IsCoprime n (q : ℤ))
  (hA : ∀ a : A, (q : ℤ) • a = 0 → a = 0) :
-- imply
  ∀ b : B, (q : ℤ) • b = 0 → b = 0 := by
-- proof
  intro b hb
  have hqψ : (q : ℤ) • ψ b = 0 := by rw [← map_zsmul, hb, map_zero]
  have hψb : ψ b = 0 := hA (ψ b) hqψ
  have hnb : n • b = 0 := hdual.ker_le_torsion_left hψb
  obtain ⟨u, v, huv⟩ := hcop
  calc _ = (1 : ℤ) • b := (one_zsmul b).symm
    _ = (u * n + v * (q : ℤ)) • b := by rw [huv]
    _ = u • n • b + v • (q : ℤ) • b := by rw [add_zsmul, mul_zsmul, mul_zsmul]
    _ = 0 := by simp [hnb, hb]


-- created on 2026-10-09
