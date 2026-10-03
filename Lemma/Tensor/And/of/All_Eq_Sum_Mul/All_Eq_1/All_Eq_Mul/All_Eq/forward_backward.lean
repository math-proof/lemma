import sympy.stats.hidden_markov_sequence
import sympy.Basic


/--
Forward-backward propagation of a linear chain.  Let `P t ys` be a family of prefix weights with
`P 0 ys = ψ₀ (ys 0)` and `P (t + 1) ys = P t ys * ψ (t + 1) (ys t) (ys (t + 1))`; no positivity or
normalization is assumed.  The hidden-Markov factorization `IsHiddenMarkovSeq` is the instance
`ψ₀ a = E 0 a * π a`, `ψ t a b = T a b * E t b`.  With the forward variable

  `z t a = ∑ ys : Fin (t + 1) → Y with ys t = a, P t ys`

and a backward variable `β` with `β m = 1` and `β t a = ∑ c, ψ (t + 1) a c * β (t + 1) c`, we get

* forward recursion: `z 0 a = ψ₀ a`, `z (t + 1) a = ∑ b, z t b * ψ (t + 1) b a`;
* forward-backward identity: `∑ ys : Fin (m + 1) → Y with ys t = a, P m ys = z t a * β t a`;
* the partition function does not depend on the cut: `∑ a, z t a * β t a = ∑ a, z m a` for `t ≤ m`.
-/
@[main]
private lemma crf.forward_backward
  {Y : Type*} [Fintype Y] [DecidableEq Y]
  {m : ℕ}
  {P : ℕ → (ℕ → Y) → ℝ}
  {ψ₀ : Y → ℝ}
  {ψ : ℕ → Y → Y → ℝ}
  {z β : ℕ → Y → ℝ}
-- given
  (h₀ : ∀ ys, P 0 ys = ψ₀ (ys 0))
  (h₁ : ∀ t ys, P (t + 1) ys = P t ys * ψ (t + 1) (ys t) (ys (t + 1)))
  (h₂ : ∀ t a, z t a = ∑ ys ∈ Finset.univ.filter (fun ys : Fin (t + 1) → Y => ys (Fin.last t) = a), P t (fun i => if h : i < t + 1 then ys ⟨i, h⟩ else a))
  (h₃ : ∀ a, β m a = 1)
  (h₄ : ∀ t < m, ∀ a, β t a = ∑ c, ψ (t + 1) a c * β (t + 1) c) :
-- imply
  (∀ a, z 0 a = ψ₀ a) ∧
    (∀ t a, z (t + 1) a = ∑ b, z t b * ψ (t + 1) b a) ∧
    (∀ t (ht : t < m + 1) a, ∑ ys ∈ Finset.univ.filter (fun ys : Fin (m + 1) → Y => ys ⟨t, ht⟩ = a), P m (fun i => if h : i < m + 1 then ys ⟨i, h⟩ else a) = z t a * β t a) ∧
    ∀ t ≤ m, ∑ a, z t a * β t a = ∑ a, z m a := by
-- proof
  have hpre : ∀ t (w w' : ℕ → Y), (∀ i ≤ t, w i = w' i) → P t w = P t w' := by
    intro t
    induction t with
    | zero =>
      intro w w' hw
      rw [h₀, h₀, hw 0 le_rfl]
    | succ t ih =>
      intro w w' hw
      rw [h₁, h₁, ih w w' (fun i hi => hw i (by omega)), hw t (by omega), hw (t + 1) le_rfl]
  have peel : ∀ (k : ℕ) (a c : Y) (Q : (ℕ → Y) → Prop) [DecidablePred Q], (∀ w w' : ℕ → Y, (∀ i ≤ k, w i = w' i) → (Q w ↔ Q w')) →
      ∑ ys : Fin (k + 1 + 1) → Y, (if Q (fun i => if h : i < k + 1 + 1 then ys ⟨i, h⟩ else a) ∧ ys (Fin.last (k + 1)) = c then P (k + 1) (fun i => if h : i < k + 1 + 1 then ys ⟨i, h⟩ else a) else 0) =
        ∑ b, ψ (k + 1) b c * ∑ ys : Fin (k + 1) → Y, (if Q (fun i => if h : i < k + 1 then ys ⟨i, h⟩ else a) ∧ ys (Fin.last k) = b then P k (fun i => if h : i < k + 1 then ys ⟨i, h⟩ else a) else 0) := by
    intro k a c Q _ hQ
    have key : ∀ (d : Y) (ys0 : Fin (k + 1) → Y),
        (if Q (fun i => if h : i < k + 1 + 1 then Fin.snoc (α := fun _ => Y) ys0 d ⟨i, h⟩ else a) ∧ Fin.snoc (α := fun _ => Y) ys0 d (Fin.last (k + 1)) = c then P (k + 1) (fun i => if h : i < k + 1 + 1 then Fin.snoc (α := fun _ => Y) ys0 d ⟨i, h⟩ else a) else 0) =
          if d = c then (if Q (fun i => if h : i < k + 1 then ys0 ⟨i, h⟩ else a) then P k (fun i => if h : i < k + 1 then ys0 ⟨i, h⟩ else a) * ψ (k + 1) (ys0 (Fin.last k)) c else 0) else 0 := by
      intro d ys0
      have hext : ∀ i, i ≤ k → (if h : i < k + 1 + 1 then Fin.snoc (α := fun _ => Y) ys0 d ⟨i, h⟩ else a) = if h : i < k + 1 then ys0 ⟨i, h⟩ else a := by
        intro i hi
        rw [dite_snoc_eq ys0 d a (by omega), dif_pos (by omega), dif_pos (by omega)]
      have hQ' : Q (fun i => if h : i < k + 1 + 1 then Fin.snoc (α := fun _ => Y) ys0 d ⟨i, h⟩ else a) ↔ Q (fun i => if h : i < k + 1 then ys0 ⟨i, h⟩ else a) :=
        hQ _ _ hext
      have hP : P (k + 1) (fun i => if h : i < k + 1 + 1 then Fin.snoc (α := fun _ => Y) ys0 d ⟨i, h⟩ else a) = P k (fun i => if h : i < k + 1 then ys0 ⟨i, h⟩ else a) * ψ (k + 1) (ys0 (Fin.last k)) d := by
        rw [h₁]
        congr 1
        · apply hpre
          intro i hi
          exact hext i hi
        · have e1 : (if h : k < k + 1 + 1 then Fin.snoc (α := fun _ => Y) ys0 d ⟨k, h⟩ else a) = ys0 (Fin.last k) := by
            rw [hext k le_rfl, dif_pos (by omega)]
            rfl
          have e2 : (if h : k + 1 < k + 1 + 1 then Fin.snoc (α := fun _ => Y) ys0 d ⟨k + 1, h⟩ else a) = d := by
            rw [dite_snoc_eq ys0 d a le_rfl, dif_neg (lt_irrefl _)]
          simp only [e1, e2]
      rw [hP, Fin.snoc_last]
      by_cases hd : d = c
      · subst hd
        simp only [and_true, if_true]
        exact if_congr hQ' rfl rfl
      · rw [if_neg hd, if_neg (fun h => hd h.2)]
    rw [Fintype.sum_snoc]
    simp only [key]
    rw [Finset.sum_eq_single c (fun d _ hd => by simp [hd]) (by simp)]
    simp only [if_true, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ys _ => ?_
    by_cases hq : Q (fun i => if h : i < k + 1 then ys ⟨i, h⟩ else a)
    · simp only [hq, true_and, if_true, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ]
      ring
    · simp only [hq, false_and, if_false, mul_zero, Finset.sum_const_zero]
  have hz₀ : ∀ a, z 0 a = ψ₀ a := by
    intro a
    rw [h₂, Finset.sum_eq_single (fun _ => a)]
    · rw [h₀]
      simp
    · intro b hb hne
      exfalso
      apply hne
      funext i
      have : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      rw [this]
      exact (Finset.mem_filter.1 hb).2
    · intro h
      exfalso
      apply h
      simp
  have hzrec : ∀ t a, z (t + 1) a = ∑ b, z t b * ψ (t + 1) b a := by
    intro t a
    have h := peel t a a (fun _ => True) (fun _ _ _ => Iff.rfl)
    simp only [true_and] at h
    rw [h₂, Finset.sum_filter, h]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h₂ t b, Finset.sum_filter, mul_comm _ (ψ (t + 1) b a)]
    congr 1
    refine Finset.sum_congr rfl fun ys _ => ?_
    split_ifs with hy
    · apply hpre
      intro i hi
      rw [dif_pos (by omega), dif_pos (by omega)]
    · rfl
  have hadj : ∀ (n t : ℕ) (U : ℕ → Y → ℝ), t + n = m → (∀ j, t ≤ j → ∀ c, U (j + 1) c = ∑ b, U j b * ψ (j + 1) b c) → ∑ c, U m c = ∑ a, U t a * β t a := by
    intro n
    induction n with
    | zero =>
      intro t U ht hU
      obtain rfl : t = m := by omega
      simp only [h₃, mul_one]
    | succ n ih =>
      intro t U ht hU
      rw [ih (t + 1) U (by omega) (fun j hj => hU j (by omega))]
      have hb := h₄ t (by omega)
      calc
        _ = ∑ a, (∑ b, U t b * ψ (t + 1) b a) * β (t + 1) a := Finset.sum_congr rfl fun a _ => by rw [hU t le_rfl]
        _ = ∑ b, U t b * ∑ a, ψ (t + 1) b a * β (t + 1) a := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
        _ = _ := Finset.sum_congr rfl fun b _ => by rw [hb b]
  have h₅ : ∀ t (ht : t < m + 1) a, ∑ ys ∈ Finset.univ.filter (fun ys : Fin (m + 1) → Y => ys ⟨t, ht⟩ = a), P m (fun i => if h : i < m + 1 then ys ⟨i, h⟩ else a) = z t a * β t a := by
    intro t ht a
    obtain ⟨U, hUdef⟩ : ∃ U : ℕ → Y → ℝ, ∀ j c, U j c = ∑ ys : Fin (j + 1) → Y, (if (fun i => if h : i < j + 1 then ys ⟨i, h⟩ else a) t = a ∧ ys (Fin.last j) = c then P j (fun i => if h : i < j + 1 then ys ⟨i, h⟩ else a) else 0) := ⟨_, fun _ _ => rfl⟩
    have hrec : ∀ j, t ≤ j → ∀ c, U (j + 1) c = ∑ b, U j b * ψ (j + 1) b c := by
      intro j hj c
      have := peel j a c (fun w => w t = a) (fun w w' hw => by rw [hw t hj])
      rw [hUdef, this]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hUdef, mul_comm]
    have hUt : ∀ c, U t c = if c = a then z t a else 0 := by
      intro c
      have hEt : ∀ ys : Fin (t + 1) → Y, (fun i => if h : i < t + 1 then ys ⟨i, h⟩ else a) t = ys (Fin.last t) := by
        intro ys
        show (if h : t < t + 1 then ys ⟨t, h⟩ else a) = _
        rw [dif_pos (Nat.lt_succ_self t)]
        rfl
      rw [hUdef, h₂, Finset.sum_filter]
      by_cases hc : c = a
      · subst hc
        rw [if_pos rfl]
        refine Finset.sum_congr rfl fun ys _ => ?_
        simp only [hEt, and_self]
      · rw [if_neg hc]
        refine Finset.sum_eq_zero fun ys _ => ?_
        simp only [hEt]
        rw [if_neg (fun h => hc (h.2.symm.trans h.1))]
    have hsum : ∑ c, U m c = ∑ ys ∈ Finset.univ.filter (fun ys : Fin (m + 1) → Y => ys ⟨t, ht⟩ = a), P m (fun i => if h : i < m + 1 then ys ⟨i, h⟩ else a) := by
      simp only [hUdef]
      rw [Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ys _ => ?_
      simp only [dif_pos ht]
      by_cases hq : ys ⟨t, ht⟩ = a
      · simp only [hq, true_and, if_true, Finset.sum_ite_eq, Finset.mem_univ]
      · simp only [hq, false_and, if_false, Finset.sum_const_zero]
    rw [← hsum, hadj (m - t) t U (by omega) hrec]
    simp only [hUt, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨hz₀, hzrec, h₅, fun t ht => ?_⟩
  rw [hadj (m - t) t z (by omega) (fun j _ c => hzrec j c)]


-- created on 2026-10-03
