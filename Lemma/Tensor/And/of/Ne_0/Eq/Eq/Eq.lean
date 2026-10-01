import sympy.stats.hidden_markov_sequence
import sympy.Basic


@[main]
private lemma crf.viterbi
  {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {n : ℕ}
  {P : ℕ → (ℕ → Y) → ℝ}
  {π : Y → ℝ}
  {T : Y → Y → ℝ}
  {E : ℕ → Y → ℝ}
  {s : ℕ → (ℕ → Y) → ℝ}
  {x : ℕ → Y → ℝ}
  {G : Y → Y → ℝ}
  {x' : ℕ → Y → ℝ}
-- given
  (_h₀ : IsHiddenMarkovSeq P π T E)
  (_h₁ : ∀ t ys, 0 < P t ys)
  (_h₂ : ∀ t ys, s t ys = Real.log (P t ys))
  (_h₃ : ∀ t a, x t a = Real.log (E t a))
  (_h₄ : ∀ a b, G a b = Real.log (T b a))
  (_h₅ : ∀ t a, x' t a = Finset.univ.sup' Finset.univ_nonempty (fun ys : Fin t → Y => s t (fun i => if h : i < t then ys ⟨i, h⟩ else a)))
  (hT : ∀ a b, 0 < T a b)
  (hE : ∀ t a, 0 < E t a)
  (hn : 0 < n) :
-- imply
  (∀ t a, 0 < t → x' t a = x t a + Finset.univ.sup' Finset.univ_nonempty (fun b => x' (t - 1) b + G a b)) ∧
    Finset.univ.sup' Finset.univ_nonempty (fun ys : Fin n → Y => P (n - 1) (fun i => if h : i < n then ys ⟨i, h⟩ else Classical.arbitrary Y)) =
      Real.exp (Finset.univ.sup' Finset.univ_nonempty (fun b => x' (n - 1) b)) := by
-- proof
  have hpre := _h₀.prefix
  have hstep : ∀ t a b (ys0 : Fin t → Y),
      s (t + 1) (fun i => if h : i < t + 1 then Fin.snoc (α := fun _ => Y) ys0 b ⟨i, h⟩ else a) =
        s t (fun i => if h : i < t then ys0 ⟨i, h⟩ else b) + G a b + x (t + 1) a := by
    intro t a b ys0
    rw [_h₂, _h₂, (_h₀ _).2 t, hpre t _ _ fun i hi => dite_snoc_eq ys0 b a hi]
    beta_reduce
    rw [dif_neg (lt_irrefl (t + 1)), dif_pos (Nat.lt_succ_self t), Fin.snoc_mk_last,
      Real.log_mul (_h₁ _ _).ne' (mul_pos (hT b a) (hE _ a)).ne', Real.log_mul (hT b a).ne' (hE _ a).ne', _h₄, _h₃]
    ring
  refine ⟨fun t a ht => ?_, ?_⟩
  ·
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [Nat.add_sub_cancel, _h₅, Finset.sup'_snoc]
    simp only [hstep, Finset.sup'_add_const_real]
    rw [add_comm]
    congr 1
    refine Finset.sup'_congr _ rfl fun b _ => ?_
    rw [_h₅]
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Finset.sup'_snoc,
      Finset.apply_sup'_eq_sup'_comp _ Real.exp (fun u v => Real.exp_monotone.map_sup u v)]
    refine Finset.sup'_congr _ rfl fun b _ => ?_
    rw [Function.comp_apply, _h₅, Finset.apply_sup'_eq_sup'_comp _ Real.exp (fun u v => Real.exp_monotone.map_sup u v)]
    refine Finset.sup'_congr _ rfl fun ys0 _ => ?_
    rw [Function.comp_apply, _h₂, Real.exp_log (_h₁ _ _)]
    exact hpre m _ _ fun i hi => dite_snoc_eq ys0 b _ hi


-- created on 2026-09-27
