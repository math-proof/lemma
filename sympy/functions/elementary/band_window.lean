import sympy.functions.elementary.masked_softmax
import sympy.concrete.expr_with_limits
import Mathlib.Tactic

/-! Band-part masks as compact windows: row `i` of the band `i − l < j < i + u` is `[β, ζ)`, `β = relu(i − l + 1)`, `ζ = min(n, i + u)`. -/

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

/-- masked softmax over the band, written over the compact window `[β, ζ)`. -/
theorem softmax_window {n : ℕ} (i : Fin n) (l u : ℕ) (a v : Fin n → ℝ) :
    ∑ j, maskedSoftmax a (fun j : Fin n => if ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u) then 1 else 0) j * v j =
      ∑ j' : Fin (min n (i.val + u) - (i.val + 1 - l)),
        Real.exp (a ⟨i.val + 1 - l + j', by have := j'.2; omega⟩) /
          (∑ k' : Fin (min n (i.val + u) - (i.val + 1 - l)), Real.exp (a ⟨i.val + 1 - l + k', by have := k'.2; omega⟩)) *
          v ⟨i.val + 1 - l + j', by have := j'.2; omega⟩ := by
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p <;> simp [maskedExp, hp]
  simp only [maskedSoftmax, key, ite_div, zero_div, ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_filter, sum_filter_eq_window i l u, sum_filter_eq_window i l u]


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

/-- masked softmax over the dilated band, written over the compact stride-`d` window. -/
theorem softmax_dilated {n : ℕ} (i : Fin n) (l u d b : ℕ) (hd : 0 < d)
    (hb1 : (i.val : ℤ) < b + l) (hb2 : ((b : ℤ) - i.val) % d = 0)
    (hb3 : ∀ j : ℕ, (i.val : ℤ) < j + l → ((j : ℤ) - i.val) % d = 0 → b ≤ j) (a v : Fin n → ℝ) :
    ∑ j, maskedSoftmax a (fun j : Fin n => if ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧
        ((j.val : ℤ) - (i.val : ℤ)) % d = 0) then 1 else 0) j * v j =
      ∑ m : Fin ((min n (i.val + u) - b + d - 1) / d),
        Real.exp (a ⟨b + m * d, by have := win_lt hd m.2; omega⟩) /
          (∑ m' : Fin ((min n (i.val + u) - b + d - 1) / d), Real.exp (a ⟨b + m' * d, by have := win_lt hd m'.2; omega⟩)) *
          v ⟨b + m * d, by have := win_lt hd m.2; omega⟩ := by
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p <;> simp [maskedExp, hp]
  simp only [maskedSoftmax, key, ite_div, zero_div, ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_filter, sum_filter_eq_dilated i l u d b hd hb1 hb2 hb3,
    sum_filter_eq_dilated i l u d b hd hb1 hb2 hb3]


theorem ArgMax_eq_of_strict {α β : Type*} [Nonempty α] [LinearOrder β] {S : Set α} {f : α → β} {x₀ : α}
    (hx : x₀ ∈ S) (h : ∀ y ∈ S, y ≠ x₀ → f y < f x₀) : ArgMax S f = x₀ := by
  have spec := Classical.epsilon_spec (p := fun x => x ∈ S ∧ ∀ y ∈ S, f y ≤ f x)
    ⟨x₀, hx, fun y hy => by
      by_cases e : y = x₀
      · rw [e]
      · exact (h y hy e).le⟩
  by_contra hne
  exact absurd (spec.2 x₀ hx) (not_le.mpr (h _ spec.1 hne))

/-- argmax of a masked softmax row versus argmax of the log-softmax row `zr` stored at offsets `off j`. -/
theorem argmax_shift {n : ℕ} [NeZero n] (P : Fin n → Prop) [DecidablePred P] (a : Fin n → ℝ) (zr : ℤ → ℝ)
    (off : Fin n → ℤ) (S : Set ℤ)
    (hS : ∀ j, P j → off j ∈ S)
    (hz : ∀ j, P j → zr (off j) = a j - Real.log (∑ k ∈ Finset.univ.filter P, Real.exp (a k)))
    (huniq : ∃ j₀, P j₀ ∧ ∀ j, P j → j ≠ j₀ → a j < a j₀)
    (hpad : ∀ o ∈ S, (¬ ∃ j, P j ∧ off j = o) → ∀ j, P j → zr o < zr (off j)) :
    ∃ j₀, ArgMax Set.univ (maskedSoftmax a (fun j => if P j then 1 else 0)) = j₀ ∧ ArgMax S zr = off j₀ := by
  obtain ⟨j₀, hP₀, hmax⟩ := huniq
  have hD : 0 < ∑ k, maskedExp (a k) (if P k then 1 else 0) := by
    refine lt_of_lt_of_le (Real.exp_pos (a j₀)) ?_
    have : maskedExp (a j₀) (if P j₀ then 1 else 0) = Real.exp (a j₀) := by simp [maskedExp, hP₀]
    rw [← this]
    exact Finset.single_le_sum (f := fun k => maskedExp (a k) (if P k then 1 else 0))
      (fun k _ => by unfold maskedExp; split_ifs <;> positivity) (Finset.mem_univ j₀)
  refine ⟨j₀, ArgMax_eq_of_strict (Set.mem_univ _) (fun j _ hj => ?_), ArgMax_eq_of_strict (hS j₀ hP₀) (fun o ho hne => ?_)⟩
  · simp only [maskedSoftmax]
    apply div_lt_div_of_pos_right _ hD
    by_cases hPj : P j
    · simp only [maskedExp, hPj, hP₀, if_true]
      exact Real.exp_lt_exp.mpr (hmax j hPj hj)
    · simp only [maskedExp, hPj, hP₀, if_true, if_false]
      simp only [show ¬ ((0 : ℝ) = 1) from zero_ne_one, if_false]
      exact Real.exp_pos _
  · by_cases hex : ∃ j, P j ∧ off j = o
    · obtain ⟨j, hPj, rfl⟩ := hex
      have hj : j ≠ j₀ := fun e => hne (by rw [e])
      rw [hz j hPj, hz j₀ hP₀]
      linarith [hmax j hPj hj]
    · exact hpad o ho hex j₀ hP₀

end Band
