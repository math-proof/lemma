import Mathlib.Tactic

/-! py `Stack[i](Piecewise(...))` with n blocks: the piecewise chain and its identification with the block concatenation. -/

/-- py `Piecewise((X₀[i], i < n₀), (X₁[i - n₀], i < n₀ + n₁), …, (X_m[i - n₀ - … - n_{m-1}], True))`. -/
def Tensor.stackIte {α : Type*} : (m : ℕ) → (Fin (m + 1) → ℕ) → (Fin (m + 1) → ℕ → α) → ℕ → α
  | 0, _, f, i => f 0 i
  | m + 1, s, f, i => if i < s 0 then f 0 i else Tensor.stackIte m (Fin.tail s) (Fin.tail f) (i - s 0)

theorem Tensor.stackIte_offset {α : Type*} (m : ℕ) (s : Fin (m + 1) → ℕ) (f : Fin (m + 1) → ℕ → α)
    (j : Fin (m + 1)) (k : ℕ) (hk : k < s j) :
    Tensor.stackIte m s f (∑ i : Fin j, s (Fin.castLE j.2.le i) + k) = f j k := by
  induction m with
  | zero =>
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    simp [Tensor.stackIte]
  | succ m ih =>
    refine Fin.cases ?_ (fun j' hk => ?_) j hk
    · intro hk
      have h0 : ∑ i : Fin ((0 : Fin (m + 2)) : ℕ), s (Fin.castLE (0 : Fin (m + 2)).2.le i) = 0 :=
        Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
      rw [h0, zero_add, Tensor.stackIte, if_pos hk]
    · have hsum : ∑ i : Fin (j'.succ : ℕ), s (Fin.castLE j'.succ.2.le i) =
          s 0 + ∑ i : Fin j', Fin.tail s (Fin.castLE j'.2.le i) := by
        change ∑ i : Fin ((j' : ℕ) + 1), s (Fin.castLE j'.succ.2.le i) = _
        rw [Fin.sum_univ_succ]
        rfl
      rw [hsum, Tensor.stackIte, if_neg (by omega), show s 0 + ∑ i : Fin j', Fin.tail s (Fin.castLE j'.2.le i) + k - s 0 =
        ∑ i : Fin j', Fin.tail s (Fin.castLE j'.2.le i) + k by omega]
      exact ih (Fin.tail s) (Fin.tail f) j' hk

/-- n-block form: the piecewise stack equals the block concatenation (`finSigmaFinEquiv`). -/
theorem Tensor.stackIte_eq_block {α : Type*} (m : ℕ) (s : Fin (m + 1) → ℕ) (f : Fin (m + 1) → ℕ → α) :
    (fun i : Fin (∑ j, s j) => Tensor.stackIte m s f i) =
      fun i => f (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2 := by
  funext i
  obtain ⟨p, rfl⟩ := finSigmaFinEquiv.surjective i
  rw [Equiv.symm_apply_apply, finSigmaFinEquiv_apply]
  exact Tensor.stackIte_offset m s f p.1 p.2 p.2.2
