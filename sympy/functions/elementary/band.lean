import sympy.concrete.expr_with_limits
import Mathlib.Tactic

/-! Band-part masks as compact windows (no softmax here; the hyperreal masked softmax versions live under `Lemma/Tensor/DotSoftmaxAdd_Mul_Infty`): row `i` of the band `i − l < j < i + u` is `[β, ζ)`, `β = relu(i − l + 1)`, `ζ = min(n, i + u)`. -/

namespace Band

/-- The band `i − l < j < i + u` of row `i` is the contiguous window `[β, ζ)`, `β = relu(i − l + 1)`, `ζ = min(n, i + u)`. -/
theorem sum_filter_eq_window {M : Type*} [AddCommMonoid M] {n : ℕ} (i : Fin n) (l u : ℕ) (g : Fin n → M) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => (i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u), g j =
      ∑ j' : Fin (min n (i.val + u) - (i.val + 1 - l)), g ⟨i.val + 1 - l + j', by have := j'.2; omega⟩ := by
  symm
  apply Finset.sum_bij (fun (j' : Fin (min n (i.val + u) - (i.val + 1 - l))) _ => (⟨i.val + 1 - l + j'.val, by have := j'.2; omega⟩ : Fin n))
  · intro j' _
    have := j'.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro a _ b _ h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have := b.2
    exact ⟨⟨b.val - (i.val + 1 - l), by omega⟩, Finset.mem_univ _, Fin.ext (by simp only; omega)⟩
  · intro _ _
    rfl

theorem win_lt {Z b d m : ℕ} (hd : 0 < d) (hm : m < (Z - b + d - 1) / d) : b + m * d < Z := by
  have h1 : (m + 1) * d ≤ Z - b + d - 1 := (Nat.le_div_iff_mul_le hd).mp hm
  rw [Nat.add_mul, one_mul] at h1
  omega

/-- dilated band `i − l < j < i + u`, `d ∣ j − i`: the window `b, b + d, b + 2d, …` below `min(n, i + u)`. -/
theorem sum_filter_eq_dilated {M : Type*} [AddCommMonoid M] {n : ℕ} (i : Fin n) (l u d b : ℕ) (hd : 0 < d)
    (hb1 : (i.val : ℤ) < b + l) (hb2 : ((b : ℤ) - i.val) % d = 0)
    (hb3 : ∀ j : ℕ, (i.val : ℤ) < j + l → ((j : ℤ) - i.val) % d = 0 → b ≤ j) (g : Fin n → M) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => (i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧
        ((j.val : ℤ) - i.val) % d = 0), g j =
      ∑ m : Fin ((min n (i.val + u) - b + d - 1) / d), g ⟨b + m * d, by have := win_lt hd m.2; omega⟩ := by
  symm
  apply Finset.sum_bij (fun (m : Fin ((min n (i.val + u) - b + d - 1) / d)) _ =>
    (⟨b + m.val * d, by have := win_lt hd m.2; omega⟩ : Fin n))
  · intro m _
    have h := win_lt hd m.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by push_cast; nlinarith [Nat.zero_le (m.val * d)], by omega, ?_⟩
    rw [show (((b + m.val * d : ℕ) : ℤ) - i.val) = ((b : ℤ) - i.val) + (m.val : ℤ) * d by push_cast; ring,
      Int.add_mul_emod_self_right, hb2]
  · intro m _ m' _ h
    simp only [Fin.mk.injEq, add_right_inj] at h
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd h)
  · intro j hj
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
  · intro _ _
    rfl

theorem beta_props {i l d b : ℕ} (hd : 0 < d) (hdl : (d : ℤ) ∣ (l : ℤ) - 1)
    (hb : (b : ℤ) = max ((i : ℤ) - l + 1) (((i : ℤ) - l + 1) % d)) :
    (i : ℤ) < b + l ∧ ((b : ℤ) - i) % d = 0 ∧ ∀ j : ℕ, (i : ℤ) < j + l → ((j : ℤ) - i) % d = 0 → b ≤ j := by
  set x : ℤ := (i : ℤ) - l + 1 with hx
  have hxi : (d : ℤ) ∣ x - i := by
    rw [show x - i = -((l : ℤ) - 1) by rw [hx]; ring]
    exact dvd_neg.mpr hdl
  have hxd : (x % d - i) % d = 0 := by
    rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
    exact Int.emod_eq_zero_of_dvd hxi
  refine ⟨by have := le_max_left x (x % d); omega, ?_, ?_⟩
  · rcases le_total (x % d) x with h | h
    · rw [hb, max_eq_left h]
      exact Int.emod_eq_zero_of_dvd hxi
    · rw [hb, max_eq_right h]
      exact hxd
  · intro j hj hji
    have hjx : (j : ℤ) % d = x % d := by
      have e1 := Int.dvd_of_emod_eq_zero hji
      have e2 : (d : ℤ) ∣ (j : ℤ) - x := by
        have := dvd_sub e1 hxi
        rwa [show (j : ℤ) - i - (x - i) = j - x by ring] at this
      exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd e2)
    have hjd : (j : ℤ) % d ≤ j := by
      have e := Int.emod_def (j : ℤ) d
      have : 0 ≤ (d : ℤ) * ((j : ℤ) / d) := mul_nonneg (by positivity) (Int.ediv_nonneg (by positivity) (by positivity))
      linarith
    have : (b : ℤ) ≤ j := by
      rw [hb]
      exact max_le (by omega) (hjx ▸ hjd)
    exact_mod_cast this

theorem ArgMax_eq_of_strict {α β : Type*} [Nonempty α] [LinearOrder β] {S : Set α} {f : α → β} {x₀ : α}
    (hx : x₀ ∈ S) (h : ∀ y ∈ S, y ≠ x₀ → f y < f x₀) : ArgMax S f = x₀ := by
  have spec := Classical.epsilon_spec (p := fun x => x ∈ S ∧ ∀ y ∈ S, f y ≤ f x)
    ⟨x₀, hx, fun y hy => by
      by_cases e : y = x₀
      · rw [e]
      · exact (h y hy e).le⟩
  by_contra hne
  exact absurd (spec.2 x₀ hx) (not_le.mpr (h _ spec.1 hne))

end Band


-- created on 2026-10-01
