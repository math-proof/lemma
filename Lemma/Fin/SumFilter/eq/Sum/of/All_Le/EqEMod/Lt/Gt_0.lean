import sympy.concrete.expr_with_limits
import sympy.Basic
import Lemma.Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0
open Nat


/-- dilated band `i − l < j < i + u`, `d ∣ j − i`: the window `b, b + d, b + 2d, …` below `min(n, i + u)`. -/
@[main]
private lemma main
  [AddCommMonoid M]
  {n : ℕ}
-- given
  (i : Fin n)
  (l u d b : ℕ)
  (hd : 0 < d)
  (hb1 : (i.val : ℤ) < b + l)
  (hb2 : ((b : ℤ) - i.val) % d = 0)
  (hb3 : ∀ j : ℕ, (i.val : ℤ) < j + l → ((j : ℤ) - i.val) % d = 0 → b ≤ j)
  (g : Fin n → M) :
-- imply
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => (i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧
        ((j.val : ℤ) - i.val) % d = 0), g j =
      ∑ m : Fin ((min n (i.val + u) - b + d - 1) / d), g ⟨b + m * d, by have := LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 hd m.2; omega⟩ := by
-- proof
  symm
  apply Finset.sum_bij (fun (m : Fin ((min n (i.val + u) - b + d - 1) / d)) _ =>
    (⟨b + m.val * d, by have := LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 hd m.2; omega⟩ : Fin n))
  ·
    intro m _
    have h := LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 hd m.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by push_cast; nlinarith [Nat.zero_le (m.val * d)], by omega, ?_⟩
    rw [show (((b + m.val * d : ℕ) : ℤ) - i.val) = ((b : ℤ) - i.val) + (m.val : ℤ) * d by push_cast; ring,
      Int.add_mul_emod_self_right, hb2]
  ·
    intro m _ m' _ h
    simp only [Fin.mk.injEq, add_right_inj] at h
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd h)
  ·
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨h1, h2, h3⟩ := hj
    have hbj : b ≤ j.val := hb3 j.val h1 h3
    have hdvd : (d : ℤ) ∣ ((j.val - b : ℕ) : ℤ) := by
      rw [Nat.cast_sub hbj]
      have e1 := Int.dvd_of_emod_eq_zero h3
      have e2 := Int.dvd_of_emod_eq_zero hb2
      have := dvd_sub e1 e2
      rwa [show (j.val : ℤ) - i.val - ((b : ℤ) - i.val) = (j.val : ℤ) - b by ring] at this
    have hdvd' : d ∣ j.val - b := Int.natCast_dvd_natCast.mp hdvd
    have hjb : (j.val - b) / d * d = j.val - b := Nat.div_mul_cancel hdvd'
    have hlt : j.val < min n (i.val + u) := by have := j.2; omega
    refine ⟨⟨(j.val - b) / d, ?_⟩, Finset.mem_univ _, Fin.ext (by simp only; omega)⟩
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hd, Nat.add_mul, one_mul, hjb]
    omega
  ·
    intro _ _
    rfl


-- created on 2026-10-07
