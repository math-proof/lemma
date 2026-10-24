import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.W4PathDominoTilings
open SimpleGraph
open MetaMathlibExt


namespace MetaMathlibExt

/--
[pell_eq_rec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma pell_eq_rec (n : ℕ) : pell n =
  ((Nat.rec (motive := fun (_ : ℕ) => ℕ × ℕ) (0, 1)
    (fun (_ : ℕ) (ih : ℕ × ℕ) => (ih.2, 2 * ih.2 + ih.1)) n).1) :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pell_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma pell_add_two (n : ℕ) : pell (n + 2) = 2 * pell (n + 1) + pell n :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pell_vals](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma pell_vals :
  pell 0 = 0 ∧ pell 1 = 1 ∧ pell 2 = 2 ∧ pell 3 = 5 ∧ pell 4 = 12 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pell_eq_pellNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma pell_eq_pellNumber : ∀ n : ℕ, pell n = pellNumber n := by
  suffices h : ∀ n : ℕ, pell n = pellNumber n ∧ pell (n + 1) = pellNumber (n + 1)
    from fun n => (h n).1
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e]
    have hp : pell (n + 2) = 2 * pell (n + 1) + pell n := pell_add_two n
    have hP : pellNumber (n + 2) = 2 * pellNumber (n + 1) + pellNumber n := rfl
    rw [hp, hP, h1, h0]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dval_vals](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma dval_vals : dval 0 = 1 ∧ dval 1 = 2 ∧ dval 2 = 10 ∧ dval 3 = 36 := by
  refine ⟨rfl, rfl, by decide, by decide⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dval_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma dval_recurrence (m : ℕ) :
  ((dval (m + 4) : ℕ) : ℤ) = 2 * (dval (m + 3) : ℤ) + 7 * (dval (m + 2) : ℤ)
    + 2 * (dval (m + 1) : ℤ) - (dval m : ℤ) := by
  unfold dval
  have hf2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have hf3 : Nat.fib (m + 3) = Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1)) := by
    have h : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
      have := @Nat.fib_add_two (m + 1); simpa [Nat.add_assoc] using this
    rw [h, hf2]
  have hf4 : Nat.fib (m + 4) =
    (Nat.fib m + Nat.fib (m + 1)) +
      (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1))) := by
    have h : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
      have := @Nat.fib_add_two (m + 2); simpa [Nat.add_assoc] using this
    rw [h, hf2, hf3]
  have hf5 : Nat.fib (m + 5) = (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1))) +
    ((Nat.fib m + Nat.fib (m + 1)) +
      (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1)))) := by
    have h : Nat.fib (m + 5) = Nat.fib (m + 3) + Nat.fib (m + 4) := by
      have := @Nat.fib_add_two (m + 3); simpa [Nat.add_assoc] using this
    rw [h, hf3, hf4]
  have hp2 : pell (m + 2) = 2 * pell (m + 1) + pell m := rfl
  have hp3 : pell (m + 3) = 2 * (2 * pell (m + 1) + pell m) + pell (m + 1) := by
    have : pell (m + 3) = 2 * pell (m + 2) + pell (m + 1) := rfl
    rw [this, hp2]
  have hp4 : pell (m + 4) = 2 * (2 * (2 * pell (m + 1) + pell m) + pell (m + 1)) +
    (2 * pell (m + 1) + pell m) := by
    have : pell (m + 4) = 2 * pell (m + 3) + pell (m + 2) := rfl
    rw [this, hp3, hp2]
  have hp5 : pell (m + 5) =
    2 * (2 * (2 * (2 * pell (m + 1) + pell m) + pell (m + 1)) +
      (2 * pell (m + 1) + pell m)) +
      (2 * (2 * pell (m + 1) + pell m) + pell (m + 1)) := by
    have : pell (m + 5) = 2 * pell (m + 4) + pell (m + 3) := rfl
    rw [this, hp4, hp3]
  have e1 : Nat.fib (m + 1 + 1) = Nat.fib m + Nat.fib (m + 1) := hf2
  have e2 : Nat.fib (m + 2 + 1) =
    Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1)) := by simpa using hf3
  have e3 : Nat.fib (m + 3 + 1) = (Nat.fib m + Nat.fib (m + 1)) +
    (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1))) := by simpa using hf4
  have e4 : Nat.fib (m + 4 + 1) = (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1))) +
    ((Nat.fib m + Nat.fib (m + 1)) +
      (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1)))) := by
    simpa using hf5
  rw [e1, e2, e3, e4, hp2, hp3, hp4, hp5]
  push_cast
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[boxProd_adj_unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma boxProd_adj_unfold (m : ℕ) (x y : Fin 4 × Fin m) :
  (W4 □ SimpleGraph.pathGraph m).Adj x y ↔
    (W4.Adj x.1 y.1 ∧ x.2 = y.2) ∨
      ((SimpleGraph.pathGraph m).Adj x.2 y.2 ∧ x.1 = y.1) :=
  boxProd_adj

end MetaMathlibExt

namespace MetaMathlibExt

/--
[horiz_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma horiz_card :
  ∀ U : Finset (Fin 4), Fintype.card (HorizPairing U) = wHoriz U := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_plift_prop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma card_plift_prop (p : Prop) [Decidable p] :
  Fintype.card (PLift p) = (if p then 1 else 0) := by
  by_cases h : p
  · simp only [ite_eq_left h]
    have e : PLift p ≃ Unit :=
      ⟨fun _ => (), fun _ => ⟨h⟩, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
    calc Fintype.card (PLift p) = Fintype.card Unit := Fintype.card_congr e
      _ = 1 := Fintype.card_unit
  · simp only [ite_eq_right h]
    have e : PLift p ≃ Empty :=
      ⟨fun x => (h x.down).elim, fun x => x.elim,
        fun x => (h x.down).elim, fun x => x.elim⟩
    calc Fintype.card (PLift p) = Fintype.card Empty := Fintype.card_congr e
      _ = 0 := Fintype.card_empty

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Ncount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Ncount_zero (S : Finset (Fin 4)) :
  Ncount 0 S = (if S = ∅ then 1 else 0) := by
  unfold Ncount
  change Fintype.card (PLift (S = ∅)) = _
  exact card_plift_prop _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Ncount_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Ncount_succ (m : ℕ) (S' : Finset (Fin 4)) :
  Ncount (m + 1) S' = ∑ S : Finset (Fin 4),
    (if Disjoint S S' then Ncount m S * wHoriz (Finset.univ \ (S ∪ S')) else 0) := by
  unfold Ncount
  change Fintype.card (Σ S : Finset (Fin 4),
    PLift (Disjoint S S') × Tiling m S × HorizPairing _) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Fintype.card_prod, Fintype.card_prod, card_plift_prop, horiz_card _]
  by_cases h : Disjoint S S'
  · simp only [ite_eq_left h, one_mul]
  · simp only [ite_eq_right h, zero_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sum_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma sum_support (m : ℕ) (S' : Finset (Fin 4)) (s : Finset (Finset (Fin 4)))
  (h : ∀ S : Finset (Fin 4),
    S ∉ s → (¬Disjoint S S' ∨ wHoriz (Finset.univ \ (S ∪ S')) = 0)) :
  (∑ S : Finset (Fin 4),
    (if Disjoint S S' then Ncount m S * wHoriz (Finset.univ \ (S ∪ S')) else 0))
    = ∑ S ∈ s,
      (if Disjoint S S' then Ncount m S * wHoriz (Finset.univ \ (S ∪ S')) else 0) := by
  have hsub : s ⊆ Finset.univ := Finset.subset_univ s
  have h0 : ∀ S ∈ (Finset.univ : Finset (Finset (Fin 4))), S ∉ s →
    (if Disjoint S S' then Ncount m S * wHoriz (Finset.univ \ (S ∪ S')) else 0) = 0 := by
    intro S _ hmem
    obtain (hdisj | hw) := h S hmem
    · simp only [ite_eq_right hdisj]
    · by_cases hdisj : Disjoint S S'
      · simp only [ite_eq_left hdisj, hw, mul_zero]
      · simp only [ite_eq_right hdisj]
  exact (Finset.sum_subset hsub h0).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Aval_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Aval_succ (m : ℕ) :
  Aval (m + 1) = 2 * Aval m + Bval m + Dval m + Eval m := by
  unfold Aval Bval Dval Eval
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
    S ∉ ({∅, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {0, 1}, Finset.univ} :
      Finset (Finset (Fin 4))) →
      (¬Disjoint S ∅ ∨ wHoriz (Finset.univ \ (S ∪ ∅)) = 0) := by decide
  rw [sum_support m ∅ _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) ∅ := by decide
  have hd1 : Disjoint ({0, 2} : Finset (Fin 4)) ∅ := by decide
  have hd2 : Disjoint ({0, 3} : Finset (Fin 4)) ∅ := by decide
  have hd3 : Disjoint ({1, 2} : Finset (Fin 4)) ∅ := by decide
  have hd4 : Disjoint ({1, 3} : Finset (Fin 4)) ∅ := by decide
  have hd5 : Disjoint ({0, 1} : Finset (Fin 4)) ∅ := by decide
  have hd6 : Disjoint (Finset.univ : Finset (Fin 4)) ∅ := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ ∅)) = 2 := by decide
  have hw1 : wHoriz (Finset.univ \ (({0, 2} : Finset (Fin 4)) ∪ ∅)) = 1 := by decide
  have hw2 : wHoriz (Finset.univ \ (({0, 3} : Finset (Fin 4)) ∪ ∅)) = 1 := by decide
  have hw3 : wHoriz (Finset.univ \ (({1, 2} : Finset (Fin 4)) ∪ ∅)) = 1 := by decide
  have hw4 : wHoriz (Finset.univ \ (({1, 3} : Finset (Fin 4)) ∪ ∅)) = 1 := by decide
  have hw5 : wHoriz (Finset.univ \ (({0, 1} : Finset (Fin 4)) ∪ ∅)) = 1 := by decide
  have hw6 : wHoriz (Finset.univ \ (Finset.univ ∪ (∅ : Finset (Fin 4)))) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, ite_eq_left hd2, ite_eq_left hd3,
    ite_eq_left hd4, ite_eq_left hd5, ite_eq_left hd6, hw0, hw1, hw2, hw3, hw4, hw5, hw6]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mixed02_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma mixed02_succ (m : ℕ) :
  Ncount (m + 1) {0, 2} = Ncount m ∅ + Ncount m {1, 3} := by
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
    S ∉ ({∅, {1, 3}} : Finset (Finset (Fin 4))) →
      (¬Disjoint S {0, 2} ∨ wHoriz (Finset.univ \ (S ∪ {0, 2})) = 0) := by decide
  rw [sum_support m {0, 2} _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) {0, 2} := by decide
  have hd1 : Disjoint ({1, 3} : Finset (Fin 4)) {0, 2} := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ {0, 2})) = 1 := by decide
  have hw1 : wHoriz (Finset.univ \ (({1, 3} : Finset (Fin 4)) ∪ {0, 2})) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, hw0, hw1]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mixed03_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma mixed03_succ (m : ℕ) :
  Ncount (m + 1) {0, 3} = Ncount m ∅ + Ncount m {1, 2} := by
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
    S ∉ ({∅, {1, 2}} : Finset (Finset (Fin 4))) →
      (¬Disjoint S {0, 3} ∨ wHoriz (Finset.univ \ (S ∪ {0, 3})) = 0) := by decide
  rw [sum_support m {0, 3} _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) {0, 3} := by decide
  have hd1 : Disjoint ({1, 2} : Finset (Fin 4)) {0, 3} := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ {0, 3})) = 1 := by decide
  have hw1 : wHoriz (Finset.univ \ (({1, 2} : Finset (Fin 4)) ∪ {0, 3})) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, hw0, hw1]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mixed12_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma mixed12_succ (m : ℕ) :
  Ncount (m + 1) {1, 2} = Ncount m ∅ + Ncount m {0, 3} := by
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
    S ∉ ({∅, {0, 3}} : Finset (Finset (Fin 4))) →
      (¬Disjoint S {1, 2} ∨ wHoriz (Finset.univ \ (S ∪ {1, 2})) = 0) := by decide
  rw [sum_support m {1, 2} _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) {1, 2} := by decide
  have hd1 : Disjoint ({0, 3} : Finset (Fin 4)) {1, 2} := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ {1, 2})) = 1 := by decide
  have hw1 : wHoriz (Finset.univ \ (({0, 3} : Finset (Fin 4)) ∪ {1, 2})) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, hw0, hw1]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mixed13_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma mixed13_succ (m : ℕ) :
  Ncount (m + 1) {1, 3} = Ncount m ∅ + Ncount m {0, 2} := by
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
    S ∉ ({∅, {0, 2}} : Finset (Finset (Fin 4))) →
      (¬Disjoint S {1, 3} ∨ wHoriz (Finset.univ \ (S ∪ {1, 3})) = 0) := by decide
  rw [sum_support m {1, 3} _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) {1, 3} := by decide
  have hd1 : Disjoint ({0, 2} : Finset (Fin 4)) {1, 3} := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ {1, 3})) = 1 := by decide
  have hw1 : wHoriz (Finset.univ \ (({0, 2} : Finset (Fin 4)) ∪ {1, 3})) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, hw0, hw1]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Bval_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Bval_succ (m : ℕ) : Bval (m + 1) = 4 * Aval m + Bval m := by
  unfold Bval Aval
  rw [mixed02_succ, mixed03_succ, mixed12_succ, mixed13_succ]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Cval_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Cval_succ (m : ℕ) : Cval (m + 1) = Dval m := by
  unfold Cval Dval
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
    S ∉ ({{0, 1}} : Finset (Finset (Fin 4))) →
      (¬Disjoint S {2, 3} ∨ wHoriz (Finset.univ \ (S ∪ {2, 3})) = 0) := by decide
  rw [sum_support m {2, 3} _ hsup]
  have hd0 : Disjoint ({0, 1} : Finset (Fin 4)) {2, 3} := by decide
  have hw0 : wHoriz (Finset.univ \ (({0, 1} : Finset (Fin 4)) ∪ {2, 3})) = 1 := by decide
  rw [Finset.sum_singleton]
  simp only [ite_eq_left hd0, hw0, mul_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Dval_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Dval_succ (m : ℕ) : Dval (m + 1) = Aval m + Cval m := by
  unfold Dval Aval Cval
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
    S ∉ ({∅, {2, 3}} : Finset (Finset (Fin 4))) →
      (¬Disjoint S {0, 1} ∨ wHoriz (Finset.univ \ (S ∪ {0, 1})) = 0) := by decide
  rw [sum_support m {0, 1} _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) {0, 1} := by decide
  have hd1 : Disjoint ({2, 3} : Finset (Fin 4)) {0, 1} := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ {0, 1})) = 1 := by decide
  have hw1 : wHoriz (Finset.univ \ (({2, 3} : Finset (Fin 4)) ∪ {0, 1})) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, hw0, hw1]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Eval_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Eval_succ (m : ℕ) : Eval (m + 1) = Aval m := by
  unfold Eval Aval
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
    S ∉ ({∅} : Finset (Finset (Fin 4))) →
      (¬Disjoint S Finset.univ ∨ wHoriz (Finset.univ \ (S ∪ Finset.univ)) = 0) := by
    decide
  rw [sum_support m Finset.univ _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) Finset.univ := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ Finset.univ)) = 1 := by decide
  rw [Finset.sum_singleton]
  simp only [ite_eq_left hd0, hw0, mul_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Aval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Aval_zero : Aval 0 = 1 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Bval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Bval_zero : Bval 0 = 0 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Cval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Cval_zero : Cval 0 = 0 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Dval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Dval_zero : Dval 0 = 0 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Eval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Eval_zero : Eval 0 = 0 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Aval_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Aval_recurrence (m : ℕ) :
  ((Aval (m + 4) : ℕ) : ℤ) = 2 * (Aval (m + 3) : ℤ) + 7 * (Aval (m + 2) : ℤ)
    + 2 * (Aval (m + 1) : ℤ) - (Aval m : ℤ) := by
  have hA0 : Aval (m + 1) = 2 * Aval m + Bval m + Dval m + Eval m := Aval_succ m
  have hA1 : Aval (m + 2) = 2 * Aval (m + 1) + Bval (m + 1) + Dval (m + 1) + Eval (m + 1) :=
    Aval_succ (m + 1)
  have hA2 : Aval (m + 3) = 2 * Aval (m + 2) + Bval (m + 2) + Dval (m + 2) + Eval (m + 2) :=
    Aval_succ (m + 2)
  have hA3 : Aval (m + 4) = 2 * Aval (m + 3) + Bval (m + 3) + Dval (m + 3) + Eval (m + 3) :=
    Aval_succ (m + 3)
  have hB0 : Bval (m + 1) = 4 * Aval m + Bval m := Bval_succ m
  have hB1 : Bval (m + 2) = 4 * Aval (m + 1) + Bval (m + 1) := Bval_succ (m + 1)
  have hB2 : Bval (m + 3) = 4 * Aval (m + 2) + Bval (m + 2) := Bval_succ (m + 2)
  have hC0 : Cval (m + 1) = Dval m := Cval_succ m
  have hC1 : Cval (m + 2) = Dval (m + 1) := Cval_succ (m + 1)
  have hC2 : Cval (m + 3) = Dval (m + 2) := Cval_succ (m + 2)
  have hD0 : Dval (m + 1) = Aval m + Cval m := Dval_succ m
  have hD1 : Dval (m + 2) = Aval (m + 1) + Cval (m + 1) := Dval_succ (m + 1)
  have hD2 : Dval (m + 3) = Aval (m + 2) + Cval (m + 2) := Dval_succ (m + 2)
  have hE0 : Eval (m + 1) = Aval m := Eval_succ m
  have hE1 : Eval (m + 2) = Aval (m + 1) := Eval_succ (m + 1)
  have hE2 : Eval (m + 3) = Aval (m + 2) := Eval_succ (m + 2)
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Aval_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Aval_one : Aval 1 = 2 := by
  have hA0 : Aval 1 = 2 * Aval 0 + Bval 0 + Dval 0 + Eval 0 := Aval_succ 0
  have ha0 := Aval_zero
  have hb0 := Bval_zero
  have hd0 := Dval_zero
  have he0 := Eval_zero
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Aval_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Aval_two : Aval 2 = 10 := by
  have hA0 : Aval 1 = 2 * Aval 0 + Bval 0 + Dval 0 + Eval 0 := Aval_succ 0
  have hA1 : Aval 2 = 2 * Aval 1 + Bval 1 + Dval 1 + Eval 1 := Aval_succ 1
  have hB0 : Bval 1 = 4 * Aval 0 + Bval 0 := Bval_succ 0
  have hD0 : Dval 1 = Aval 0 + Cval 0 := Dval_succ 0
  have hE0 : Eval 1 = Aval 0 := Eval_succ 0
  have ha0 := Aval_zero
  have hb0 := Bval_zero
  have hc0 := Cval_zero
  have hd0 := Dval_zero
  have he0 := Eval_zero
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Aval_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Aval_three : Aval 3 = 36 := by
  have hA0 : Aval 1 = 2 * Aval 0 + Bval 0 + Dval 0 + Eval 0 := Aval_succ 0
  have hA1 : Aval 2 = 2 * Aval 1 + Bval 1 + Dval 1 + Eval 1 := Aval_succ 1
  have hA2 : Aval 3 = 2 * Aval 2 + Bval 2 + Dval 2 + Eval 2 := Aval_succ 2
  have hB0 : Bval 1 = 4 * Aval 0 + Bval 0 := Bval_succ 0
  have hB1 : Bval 2 = 4 * Aval 1 + Bval 1 := Bval_succ 1
  have hC0 : Cval 1 = Dval 0 := Cval_succ 0
  have hD0 : Dval 1 = Aval 0 + Cval 0 := Dval_succ 0
  have hD1 : Dval 2 = Aval 1 + Cval 1 := Dval_succ 1
  have hE0 : Eval 1 = Aval 0 := Eval_succ 0
  have hE1 : Eval 2 = Aval 1 := Eval_succ 1
  have ha0 := Aval_zero
  have hb0 := Bval_zero
  have hc0 := Cval_zero
  have hd0 := Dval_zero
  have he0 := Eval_zero
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Aval_eq_dval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma Aval_eq_dval : ∀ m : ℕ, Aval m = dval m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h : m < 4
    · have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
      obtain rfl | rfl | rfl | rfl := hcases
      · have ha := Aval_zero
        have hd := dval_vals.1
        omega
      · have ha := Aval_one
        have hd := dval_vals.2.1
        omega
      · have ha := Aval_two
        have hd := dval_vals.2.2.1
        omega
      · have ha := Aval_three
        have hd := dval_vals.2.2.2
        omega
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      have ih0 := ih k (by omega)
      have ih1 := ih (k + 1) (by omega)
      have ih2 := ih (k + 2) (by omega)
      have ih3 := ih (k + 3) (by omega)
      have hA := Aval_recurrence k
      have hD := dval_recurrence k
      have hz : ((Aval (k + 4) : ℕ) : ℤ) = ((dval (k + 4) : ℕ) : ℤ) := by omega
      exact_mod_cast hz

end MetaMathlibExt

namespace MetaMathlibExt

/--
[below_eq_topHoles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma below_eq_topHoles (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
  (hM : M.IsPerfectMatching) (k : ℕ) :
  belowSet m M hM k = topHoles m M hM k :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[above_eq_topHoles_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma above_eq_topHoles_succ (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
  (hM : M.IsPerfectMatching) (k : ℕ) :
  aboveSet m M hM k = topHoles m M hM (k + 1) := by
  unfold aboveSet topHoles
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[getS_recurse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma getS_recurse (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling (m + 1) S')
  (j : ℕ) (hj : j ≠ m) :
  getS (m + 1) S' t j = getS m (t.1) (t.2.2.1) j := by
  cases t with
  | mk S snd =>
    cases snd with
    | mk _ rest =>
      cases rest with
      | mk t _ =>
        simp only [getS, ite_eq_right hj]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[getF_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma getF_top (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling (m + 1) S') :
  getF (m + 1) S' t m = (t.2.2.2).val := by
  cases t with
  | mk _ snd =>
    cases snd with
    | mk _ rest =>
      cases rest with
      | mk _ h =>
        simp only [getF, ite_true]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[getF_recurse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma getF_recurse (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling (m + 1) S')
  (j : ℕ) (hj : j ≠ m) :
  getF (m + 1) S' t j = getF m (t.1) (t.2.2.1) j := by
  cases t with
  | mk _ snd =>
    cases snd with
    | mk _ rest =>
      cases rest with
      | mk t _ =>
        simp only [getF, ite_eq_right hj]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[horizPairing_props](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma horizPairing_props (U : Finset (Fin 4)) (h : HorizPairing U) :
  HorizProps h.val U :=
  h.property

end MetaMathlibExt

namespace MetaMathlibExt

/--
[getF_build_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma getF_build_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
  (hM : M.IsPerfectMatching) : ∀ (k : ℕ) (hk : k ≤ m) (j : ℕ) (_hj : j < k),
  getF k (topHoles m M hM k) (buildTiling m M hM k hk) j = horizFunNat m M hM j := by
  intro k
  induction k with
  | zero =>
    intro hk j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro hk j _hj
    by_cases hjm : j = k
    · rw [hjm]
      have htop : getF (k + 1) (topHoles m M hM (k + 1))
        (buildTiling m M hM (k + 1) hk) k =
        ((buildTiling m M hM (k + 1) hk).2.2.2).val :=
        getF_top k _ _
      rw [htop]
      rfl
    · have hjk : j < k := by omega
      have hk' : k ≤ m := by omega
      have hrec : getF (k + 1) (topHoles m M hM (k + 1))
        (buildTiling m M hM (k + 1) hk) j =
        getF k ((buildTiling m M hM (k + 1) hk).1)
          ((buildTiling m M hM (k + 1) hk).2.2.1) j :=
        getF_recurse k _ _ j hjm
      rw [hrec]
      exact ih hk' j hjk

end MetaMathlibExt

namespace MetaMathlibExt

/--
[getS_rec_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma getS_rec_eq (m : ℕ) (S1 : Finset (Fin 4)) (build : Tiling m S1)
  (htop : S1 = ∅) (j : ℕ) :
  getS m ∅ (htop.rec build) j = getS m S1 build j := by
  cases htop
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[getF_rec_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma getF_rec_eq (m : ℕ) (S1 : Finset (Fin 4)) (build : Tiling m S1)
  (htop : S1 = ∅) (j : ℕ) :
  getF m ∅ (htop.rec build) j = getF m S1 build j := by
  cases htop
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[boxProd_tiling_card_eq_fib_mul_pell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
lemma boxProd_tiling_card_eq_fib_mul_pell
  :
-- imply
  ∀ (n : ℕ) (_hn : 2 ≤ n),
    Nat.card { M : (((SimpleGraph.completeGraph (Fin 4)).deleteEdges
    {Sym2.mk (0 : Fin 4) (1 : Fin 4)} □
    SimpleGraph.pathGraph (n - 1)).Subgraph) // M.IsPerfectMatching } =
    Nat.fib n *
    ((Nat.rec (motive := by
-- proof
  intro n hn
  have h := boxProd_tiling_card_eq_fib_mul_pellNumber n hn
  rw [h]
  congr 1
  exact (pell_eq_pellNumber n).symm
end MetaMathlibExt


/--
[boxProd_tiling_card_eq_fib_mul_pellNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean)
-/
@[path]
private lemma boxProd_tiling_card_eq_fib_mul_pellNumber_eq
  :
-- imply
  ∀ (n : ℕ) (_hn : 2 ≤ n),
    Nat.card { M : (((SimpleGraph.completeGraph (Fin 4)).deleteEdges
    {Sym2.mk (0 : Fin 4) (1 : Fin 4)} □
    SimpleGraph.pathGraph (n - 1)).Subgraph) // M.IsPerfectMatching } =
    Nat.fib n * pellNumber n := by
-- proof
  apply MetaMathlibExt.boxProd_tiling_card_eq_fib_mul_pellNumber


-- created on 2026-10-20
-- updated on 2026-10-23
