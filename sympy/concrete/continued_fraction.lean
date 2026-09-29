import sympy.concrete.continuant

/-!
SymPy's continued fraction `alpha` (`Lemma/Finset/Alpha/gt/Zero.py`):
`alpha(x[:1]) = x[0]`, `alpha(x[:n]) = x[0] + 1 / alpha(x[1:n])`; the multi-argument form
`alpha(x[:n], y, …)` is `alpha` of the concatenated argument list.
Here the argument is a `List`; `alpha [] = 0` is a junk value.
-/

namespace Continuant

def alpha {R : Type*} [Field R] : List R → R
  | [] => 0
  | [a] => a
  | a :: b :: l => a + 1 / alpha (b :: l)

theorem alpha_cons {R : Type*} [Field R] (c : R) : ∀ {m : List R}, m ≠ [] → alpha (c :: m) = c + 1 / alpha m
  | _ :: _, _ => rfl

theorem alpha_append_pair {R : Type*} [Field R] (l : List R) (a b : R) :
    alpha (l ++ [a, b]) = alpha (l ++ [a + 1 / b]) := by
  induction l with
  | nil => simp [alpha]
  | cons c l ih =>
    rw [List.cons_append, List.cons_append, alpha_cons _ (by simp), alpha_cons _ (by simp), ih]

theorem ofFn_eq_map_range {R : Type*} (x : ℕ → R) (n : ℕ) :
    List.ofFn (fun i : Fin n => x i) = (List.range n).map x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.range_succ, List.map_append, ← ih]
    rfl

theorem alpha_pos : ∀ {l : List ℝ}, l ≠ [] → (∀ a ∈ l, 0 < a) → 0 < alpha l
  | [], hl, _ => absurd rfl hl
  | [a], _, h => by simpa [alpha] using h a (by simp)
  | a :: b :: l, _, h => by
    have ih := alpha_pos (l := b :: l) (by simp) (fun c hc => h c (List.mem_cons_of_mem a hc))
    have ha := h a (by simp)
    exact add_pos ha (one_div_pos.mpr ih)

theorem K_nonneg_pos (x : ℕ → ℝ) (h : ∀ i, 0 < x i) : ∀ m, 0 ≤ K x m ∧ 0 < K x (m + 1)
  | 0 => ⟨by simp [K], by simp [K]⟩
  | m + 1 => by
    have ih := K_nonneg_pos x h m
    exact ⟨ih.2.le, show 0 < K x (m + 1) * x (m + 1) + K x m from
      add_pos_of_pos_of_nonneg (mul_pos ih.2 (h (m + 1))) ih.1⟩

theorem H_pos (x : ℕ → ℝ) (h : ∀ i, 0 < x i) (m : ℕ) : 0 < H x m := by
  have key : ∀ m, 0 < H x m ∧ 0 < H x (m + 1) := by
    intro m
    induction m with
    | zero => exact ⟨by simp [H], by simpa [H] using h 0⟩
    | succ m ih =>
      exact ⟨ih.2, show 0 < H x (m + 1) * x (m + 1) + H x m from
        add_pos (mul_pos ih.2 (h (m + 1))) ih.1⟩
  exact (key m).1

theorem alpha_append (x : ℕ → ℝ) (h : ∀ i, 0 < x i) (n : ℕ) :
    ∀ {t : ℝ}, 0 < t → alpha ((List.range (n + 1)).map x ++ [t]) =
      (H x (n + 1) * t + H x n) / (K x (n + 1) * t + K x n) := by
  induction n with
  | zero =>
    intro t ht
    have ht' := ht.ne'
    simp [alpha, H, K]
    field_simp
  | succ n ih =>
    intro t ht
    have hx := h (n + 1)
    have e : (List.range (n + 1 + 1)).map x ++ [t] = (List.range (n + 1)).map x ++ [x (n + 1), t] := by
      rw [List.range_succ (n := n + 1), List.map_append, List.append_assoc]
      rfl
    rw [e, alpha_append_pair, ih (add_pos hx (one_div_pos.mpr ht))]
    have k := K_nonneg_pos x h n
    have k' := K_nonneg_pos x h (n + 1)
    have hd1 : K x (n + 1) * (x (n + 1) + 1 / t) + K x n ≠ 0 :=
      (add_pos_of_pos_of_nonneg (mul_pos k.2 (add_pos hx (one_div_pos.mpr ht))) k.1).ne'
    have hd2 : K x (n + 1 + 1) * t + K x (n + 1) ≠ 0 :=
      (add_pos_of_pos_of_nonneg (mul_pos k'.2 ht) k'.1).ne'
    rw [div_eq_div_iff hd1 hd2]
    show (H x (n + 1) * (x (n + 1) + 1 / t) + H x n) * ((K x (n + 1) * x (n + 1) + K x n) * t + K x (n + 1)) =
      ((H x (n + 1) * x (n + 1) + H x n) * t + H x (n + 1)) * (K x (n + 1) * (x (n + 1) + 1 / t) + K x n)
    have ht' := ht.ne'
    field_simp
    ring

theorem alpha_eq (x : ℕ → ℝ) (h : ∀ i, 0 < x i) (n : ℕ) :
    alpha ((List.range (n + 1)).map x) = H x (n + 1) / K x (n + 1) := by
  cases n with
  | zero => simp [alpha, H, K]
  | succ n =>
    rw [List.range_succ (n := n + 1), List.map_append]
    exact alpha_append x h n (h (n + 1))

theorem HK_det {R : Type*} [CommRing R] (x : ℕ → R) (n : ℕ) :
    H x (n + 1) * K x n - H x n * K x (n + 1) = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp [H, K]
  | succ n ih =>
    show (H x (n + 1) * x (n + 1) + H x n) * K x (n + 1) - H x (n + 1) * (K x (n + 1) * x (n + 1) + K x n) =
      (-1) ^ (n + 1 + 1)
    rw [pow_succ]
    linear_combination (-1 : R) * ih

end Continuant
