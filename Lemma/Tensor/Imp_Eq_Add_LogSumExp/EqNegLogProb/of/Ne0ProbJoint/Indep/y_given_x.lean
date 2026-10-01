import sympy.stats.hidden_markov_sequence
import sympy.Basic


@[main]
private lemma main
  {Y : Type*} [Fintype Y] [DecidableEq Y]
  {n : ℕ}
  {P : ℕ → (ℕ → Y) → ℝ}
  {π : Y → ℝ}
  {T : Y → Y → ℝ}
  {E : ℕ → Y → ℝ}
  {s : ℕ → (ℕ → Y) → ℝ}
  {x : ℕ → Y → ℝ}
  {G : Y → Y → ℝ}
  {z x' : ℕ → Y → ℝ}
  {Pyx : (ℕ → Y) → ℝ}
-- given
  (_h₀ : IsHiddenMarkovSeq P π T E)
  (_h₁ : ∀ t ys, 0 < P t ys)
  (_h₂ : ∀ t ys, s t ys = Real.log (P t ys))
  (_h₃ : ∀ t a, x t a = Real.log (E t a))
  (_h₄ : ∀ a b, G a b = Real.log (T b a))
  (_h₅ : ∀ t a, z t a = ∑ ys ∈ Finset.univ.filter (fun ys : Fin (t + 1) → Y => ys (Fin.last t) = a), Real.exp (s t (fun i => if h : i < t + 1 then ys ⟨i, h⟩ else a)))
  (_h₆ : ∀ t a, x' t a = Real.log (z t a))
  (_h₇ : ∀ ys, Pyx ys = P (n - 1) ys / ∑ ys' : Fin n → Y, P (n - 1) (fun i => if h : i < n then ys' ⟨i, h⟩ else ys i))
  (hT : ∀ a b, 0 < T a b)
  (hE : ∀ t a, 0 < E t a)
  (hn : 0 < n) :
-- imply
  (∀ t a, 0 < t → x' t a = Real.log (∑ b, Real.exp (x' (t - 1) b + G a b)) + x t a) ∧
    ∀ ys, -Real.log (Pyx ys) = Real.log (∑ b, Real.exp (x' (n - 1) b)) - s (n - 1) ys := by
-- proof
  have hpre := _h₀.prefix
  have hz : ∀ t a, z t a = ∑ ys0 : Fin t → Y, P t (fun i => if h : i < t then ys0 ⟨i, h⟩ else a) := by
    intro t a
    rw [_h₅, Finset.sum_filter, Fintype.sum_snoc]
    simp only [Fin.snoc_last]
    rw [Finset.sum_eq_single a (fun b _ hb => Finset.sum_eq_zero fun ys0 _ => if_neg hb) (by simp)]
    refine Finset.sum_congr rfl fun ys0 _ => ?_
    rw [if_pos rfl, _h₂, Real.exp_log (_h₁ _ _)]
    exact hpre t _ _ fun i hi => dite_snoc_eq ys0 a a hi
  have hzpos : ∀ t a, 0 < z t a := by
    intro t a
    have : Nonempty Y := ⟨a⟩
    rw [hz]
    exact Finset.sum_pos (fun _ _ => _h₁ _ _) Finset.univ_nonempty
  have hrec : ∀ t a, z (t + 1) a = (∑ b, z t b * T b a) * E (t + 1) a := by
    intro t a
    rw [hz, Fintype.sum_snoc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hz, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ys1 _ => ?_
    rw [(_h₀ _).2 t, hpre t _ _ fun i hi => dite_snoc_eq ys1 b a hi]
    beta_reduce
    rw [dif_neg (lt_irrefl (t + 1)), dif_pos (Nat.lt_succ_self t), Fin.snoc_mk_last]
    ring
  refine ⟨fun t a ht => ?_, fun ys => ?_⟩
  ·
    have : Nonempty Y := ⟨a⟩
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hs : ∑ b, Real.exp (x' t b + G a b) = ∑ b, z t b * T b a :=
      Finset.sum_congr rfl fun b _ => by rw [Real.exp_add, _h₆, _h₄, Real.exp_log (hzpos t b), Real.exp_log (hT b a)]
    rw [Nat.add_sub_cancel, _h₆, hrec, Real.log_mul (Finset.sum_pos (fun b _ => mul_pos (hzpos t b) (hT b a)) Finset.univ_nonempty).ne' (hE _ a).ne', hs, _h₃]
  ·
    have : Nonempty Y := ⟨ys 0⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hD : ∑ ys' : Fin (m + 1) → Y, P m (fun i => if h : i < m + 1 then ys' ⟨i, h⟩ else ys i) = ∑ b, Real.exp (x' m b) := by
      rw [Fintype.sum_snoc]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [_h₆, Real.exp_log (hzpos m b), hz]
      exact Finset.sum_congr rfl fun ys0 _ => hpre m _ _ fun i hi => dite_snoc_eq ys0 b (ys i) hi
    have hDpos : 0 < ∑ b, Real.exp (x' m b) := Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
    rw [_h₇, Nat.add_sub_cancel, hD, Real.log_div (_h₁ _ _).ne' hDpos.ne', ← _h₂]
    ring


-- created on 2026-10-01
