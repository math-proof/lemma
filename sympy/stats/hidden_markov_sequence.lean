import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-- Sequential (first-order, hidden) Markov structure of the prefix joint probabilities used by the
py CRF lemmas.  `P t ys` is `Pr(x[:t+1] = x_obs[:t+1], y[:t+1] = ys[:t+1])` for the fixed observed
sequence, `π a = Pr(y[0] = a)`, `T a b = Pr(y[i] = b | y[i-1] = a)` (time-homogeneous) and
`E i b = Pr(x[i] = x_obs[i] | y[i] = b)`.  The py independence assumptions
(`x[k] | x[:k] & y[:k] = x[k]`, `y[k] | y[:k] = y[k] | y[k-1]`, `y[k] | x[:k] = y[k]`) are used in py
only through the one-step factorization recorded here. -/
def IsHiddenMarkovSeq {Y : Type*} (P : ℕ → (ℕ → Y) → ℝ) (π : Y → ℝ) (T : Y → Y → ℝ) (E : ℕ → Y → ℝ) : Prop :=
  ∀ ys : ℕ → Y, P 0 ys = E 0 (ys 0) * π (ys 0) ∧
    ∀ t, P (t + 1) ys = P t ys * (T (ys t) (ys (t + 1)) * E (t + 1) (ys (t + 1)))

/-- `P t` only depends on the prefix `ys 0, …, ys t`. -/
theorem IsHiddenMarkovSeq.prefix {Y : Type*} {P : ℕ → (ℕ → Y) → ℝ} {π : Y → ℝ} {T : Y → Y → ℝ} {E : ℕ → Y → ℝ}
    (h : IsHiddenMarkovSeq P π T E) : ∀ t (w w' : ℕ → Y), (∀ i ≤ t, w i = w' i) → P t w = P t w' := by
  intro t
  induction t with
  | zero =>
    intro w w' hw
    rw [(h w).1, (h w').1, hw 0 le_rfl]
  | succ t ih =>
    intro w w' hw
    rw [(h w).2 t, (h w').2 t, ih w w' (fun i hi => hw i (by omega)), hw t (by omega), hw (t + 1) le_rfl]

theorem dite_snoc_eq {Y : Type*} {t : ℕ} (ys : Fin t → Y) (b a : Y) {i : ℕ} (hi : i ≤ t) :
    (if h : i < t + 1 then Fin.snoc (α := fun _ => Y) ys b ⟨i, h⟩ else a) = if h : i < t then ys ⟨i, h⟩ else b := by
  rcases hi.lt_or_eq with h | rfl
  · rw [dif_pos (by omega), dif_pos h]
    exact Fin.snoc_castSucc (α := fun _ => Y) (p := ys) (x := b) (i := ⟨i, h⟩)
  · rw [dif_pos (Nat.lt_succ_self _), dif_neg (lt_irrefl _)]
    exact Fin.snoc_last (α := fun _ => Y) (p := ys) (x := b)

theorem Fin.snoc_mk_last {Y : Type*} {t : ℕ} (ys : Fin t → Y) (b : Y) (h : t < t + 1) :
    Fin.snoc (α := fun _ => Y) ys b ⟨t, h⟩ = b :=
  Fin.snoc_last (α := fun _ => Y) (p := ys) (x := b)

theorem Fintype.sum_snoc {Y : Type*} [Fintype Y] {t : ℕ} (F : (Fin (t + 1) → Y) → ℝ) :
    ∑ ys, F ys = ∑ b, ∑ ys0 : Fin t → Y, F (Fin.snoc (α := fun _ => Y) ys0 b) := by
  rw [← (Fin.snocEquiv (fun _ => Y)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem Finset.sup'_snoc {Y : Type*} [Fintype Y] [Nonempty Y] {t : ℕ} (F : (Fin (t + 1) → Y) → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty F =
      Finset.univ.sup' Finset.univ_nonempty (fun b => Finset.univ.sup' Finset.univ_nonempty
        (fun ys0 : Fin t → Y => F (Fin.snoc (α := fun _ => Y) ys0 b))) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun ys _ => ?_
    refine Finset.le_sup'_of_le _ (Finset.mem_univ (ys (Fin.last t))) (Finset.le_sup'_of_le _ (Finset.mem_univ (Fin.init ys)) ?_)
    simp only [Fin.snoc_init_self, le_refl]
  · exact Finset.sup'_le _ _ fun b _ => Finset.sup'_le _ _ fun ys0 _ => Finset.le_sup' F (Finset.mem_univ _)

theorem Finset.sup'_add_const_real {ι : Type*} (s : Finset ι) (H : s.Nonempty) (g : ι → ℝ) (c : ℝ) :
    s.sup' H (fun i => g i + c) = s.sup' H g + c := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i hi => add_le_add_left (Finset.le_sup' g hi) c
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' H g
    rw [he]
    exact Finset.le_sup' (f := fun i => g i + c) hi


-- created on 2026-09-27
