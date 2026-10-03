import Lemma.Tensor.ArgMaxItemGetSoftmaxAdd_Mul_Infty.eq.Shift
import sympy.concrete.expr_with_limits
import sympy.Basic
open Tensor Hyperreal
set_option maxHeartbeats 1000000


@[main]
private lemma lower_triangle.tf
  {n l : ℕ}
  [NeZero n]
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k)))
  (h_uniq : ∀ i : Fin n, ∃ j₀ : Fin n, ((i.val : ℤ) - l < (j₀.val : ℤ) ∧ (j₀.val : ℤ) ≤ i.val) ∧ ∀ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → (j ≠ j₀) → A i j < A i j₀)
  (h_pad : ∀ (i : Fin n) (o : ℤ), (o ∈ Set.Ico (0 : ℤ) l) → (¬ ∃ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) ∧ (j.val : ℤ) - i.val + ((l : ℤ) - 1) = o) → ∀ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → (z i o < z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))))
  (h_l : 0 < l) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] (A i j : Tensor ℝ []) : Tensor ℝ [n, n])
  ∀ i : Fin n, ((ArgMax Set.univ (fun j : Fin n => (((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []).item) : Fin n) : ℤ) - i.val = ArgMax (Set.Ico (0 : ℤ) l) (z i) - ((l : ℤ) - 1) := by
-- proof
  intro Ξ A₀ i
  obtain ⟨j₀, e1, e2⟩ := ArgMaxItemGetSoftmaxAdd_Mul_Infty.eq.Shift (h_ne := fun i => ⟨i, by omega⟩) (fun (i' j : Fin n) => ((i'.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i'.val)) A i (z i)
    (fun j : Fin n => (j.val : ℤ) - i.val + ((l : ℤ) - 1)) (Set.Ico (0 : ℤ) l) (fun j hj => by simp only [Set.mem_Ico]; omega) (fun j hj => h i j hj)
    (h_uniq i) (h_pad i)
  rw [e1, e2]
  ring


@[main]
private lemma lower_triangle
  {n l : ℕ}
  [NeZero n]
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k)))
  (h_uniq : ∀ i : Fin n, ∃ j₀ : Fin n, ((i.val : ℤ) - l < (j₀.val : ℤ) ∧ (j₀.val : ℤ) ≤ i.val) ∧ ∀ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → (j ≠ j₀) → A i j < A i j₀)
  (h_pad : ∀ (i : Fin n) (o : ℤ), (o ∈ Set.Ico (0 : ℤ) l) → (¬ ∃ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) ∧ (j.val : ℤ) - i.val + ((l : ℤ) - 1) = o) → ∀ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → (z i o < z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))))
  (h_l : 0 < l) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] (A i j : Tensor ℝ []) : Tensor ℝ [n, n])
  ∀ i : Fin n, ((ArgMax Set.univ (fun j : Fin n => (((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []).item) : Fin n) : ℤ) - i.val = ArgMax (Set.Ico (0 : ℤ) l) (z i) - ((l : ℤ) - 1) := by
-- proof
  intro Ξ A₀ i
  obtain ⟨j₀, e1, e2⟩ := ArgMaxItemGetSoftmaxAdd_Mul_Infty.eq.Shift (h_ne := fun i => ⟨i, by omega⟩) (fun (i' j : Fin n) => ((i'.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i'.val)) A i (z i)
    (fun j : Fin n => (j.val : ℤ) - i.val + ((l : ℤ) - 1)) (Set.Ico (0 : ℤ) l) (fun j hj => by simp only [Set.mem_Ico]; omega) (fun j hj => h i j hj)
    (h_uniq i) (h_pad i)
  rw [e1, e2]
  ring


@[main]
private lemma tf
  {n l u : ℕ}
  [NeZero n]
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k)))
  (h_uniq : ∀ i : Fin n, ∃ j₀ : Fin n, ((i.val : ℤ) - l < (j₀.val : ℤ) ∧ (j₀.val : ℤ) < (i.val : ℤ) + u) ∧ ∀ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → (j ≠ j₀) → A i j < A i j₀)
  (h_pad : ∀ (i : Fin n) (o : ℤ), (o ∈ Set.Ico (0 : ℤ) ((l : ℤ) + u - 1)) → (¬ ∃ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) ∧ (j.val : ℤ) - i.val + ((l : ℤ) - 1) = o) → ∀ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → (z i o < z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))))
  (h_l : 0 < l)
  (h_u : 0 < u) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] (A i j : Tensor ℝ []) : Tensor ℝ [n, n])
  ∀ i : Fin n, ((ArgMax Set.univ (fun j : Fin n => (((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []).item) : Fin n) : ℤ) - i.val = ArgMax (Set.Ico 0 ((l : ℤ) + u - 1)) (z i) - ((l : ℤ) - 1) := by
-- proof
  intro Ξ A₀ i
  obtain ⟨j₀, e1, e2⟩ := ArgMaxItemGetSoftmaxAdd_Mul_Infty.eq.Shift (h_ne := fun i => ⟨i, by omega⟩) (fun (i' j : Fin n) => ((i'.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i'.val : ℤ) + u)) A i (z i)
    (fun j : Fin n => (j.val : ℤ) - i.val + ((l : ℤ) - 1)) (Set.Ico 0 ((l : ℤ) + u - 1)) (fun j hj => by simp only [Set.mem_Ico]; omega) (fun j hj => h i j hj)
    (h_uniq i) (h_pad i)
  rw [e1, e2]
  ring


@[main]
private lemma main
  {n l u : ℕ}
  [NeZero n]
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k)))
  (h_uniq : ∀ i : Fin n, ∃ j₀ : Fin n, ((i.val : ℤ) - l < (j₀.val : ℤ) ∧ (j₀.val : ℤ) < (i.val : ℤ) + u) ∧ ∀ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → (j ≠ j₀) → A i j < A i j₀)
  (h_pad : ∀ (i : Fin n) (o : ℤ), (o ∈ Set.Ico (0 : ℤ) ((l : ℤ) + u - 1)) → (¬ ∃ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) ∧ (j.val : ℤ) - i.val + ((l : ℤ) - 1) = o) → ∀ j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → (z i o < z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))))
  (h_l : 0 < l)
  (h_u : 0 < u) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] (A i j : Tensor ℝ []) : Tensor ℝ [n, n])
  ∀ i : Fin n, ((ArgMax Set.univ (fun j : Fin n => (((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []).item) : Fin n) : ℤ) - i.val = ArgMax (Set.Ico 0 ((l : ℤ) + u - 1)) (z i) - ((l : ℤ) - 1) := by
-- proof
  intro Ξ A₀ i
  obtain ⟨j₀, e1, e2⟩ := ArgMaxItemGetSoftmaxAdd_Mul_Infty.eq.Shift (h_ne := fun i => ⟨i, by omega⟩) (fun (i' j : Fin n) => ((i'.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i'.val : ℤ) + u)) A i (z i)
    (fun j : Fin n => (j.val : ℤ) - i.val + ((l : ℤ) - 1)) (Set.Ico 0 ((l : ℤ) + u - 1)) (fun j hj => by simp only [Set.mem_Ico]; omega) (fun j hj => h i j hj)
    (h_uniq i) (h_pad i)
  rw [e1, e2]
  ring


@[main]
private lemma upper_triangle.tf
  {n u : ℕ}
  [NeZero n]
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) ≤ (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k)))
  (h_uniq : ∀ i : Fin n, ∃ j₀ : Fin n, ((i.val : ℤ) ≤ (j₀.val : ℤ) ∧ (j₀.val : ℤ) < (i.val : ℤ) + u) ∧ ∀ j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → (j ≠ j₀) → A i j < A i j₀)
  (h_pad : ∀ (i : Fin n) (o : ℤ), (o ∈ Set.Ico (0 : ℤ) (u : ℤ)) → (¬ ∃ j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) ∧ (j.val : ℤ) - i.val = o) → ∀ j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → (z i o < z i ((j.val : ℤ) - i.val)))
  (h_u : 0 < u) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] (A i j : Tensor ℝ []) : Tensor ℝ [n, n])
  ∀ i : Fin n, ((ArgMax Set.univ (fun j : Fin n => (((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []).item) : Fin n) : ℤ) - i.val = ArgMax (Set.Ico 0 (u : ℤ)) (z i) := by
-- proof
  intro Ξ A₀ i
  obtain ⟨j₀, e1, e2⟩ := ArgMaxItemGetSoftmaxAdd_Mul_Infty.eq.Shift (h_ne := fun i => ⟨i, by omega⟩) (fun (i' j : Fin n) => ((i'.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i'.val : ℤ) + u)) A i (z i)
    (fun j : Fin n => (j.val : ℤ) - i.val) (Set.Ico 0 (u : ℤ)) (fun j hj => by simp only [Set.mem_Ico]; omega) (fun j hj => h i j hj)
    (h_uniq i) (h_pad i)
  rw [e1, e2]


@[main]
private lemma upper_triangle
  {n u : ℕ}
  [NeZero n]
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) ≤ (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k)))
  (h_uniq : ∀ i : Fin n, ∃ j₀ : Fin n, ((i.val : ℤ) ≤ (j₀.val : ℤ) ∧ (j₀.val : ℤ) < (i.val : ℤ) + u) ∧ ∀ j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → (j ≠ j₀) → A i j < A i j₀)
  (h_pad : ∀ (i : Fin n) (o : ℤ), (o ∈ Set.Ico (0 : ℤ) (u : ℤ)) → (¬ ∃ j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) ∧ (j.val : ℤ) - i.val = o) → ∀ j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → (z i o < z i ((j.val : ℤ) - i.val)))
  (h_u : 0 < u) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] (A i j : Tensor ℝ []) : Tensor ℝ [n, n])
  ∀ i : Fin n, ((ArgMax Set.univ (fun j : Fin n => (((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []).item) : Fin n) : ℤ) - i.val = ArgMax (Set.Ico 0 (u : ℤ)) (z i) := by
-- proof
  intro Ξ A₀ i
  obtain ⟨j₀, e1, e2⟩ := ArgMaxItemGetSoftmaxAdd_Mul_Infty.eq.Shift (h_ne := fun i => ⟨i, by omega⟩) (fun (i' j : Fin n) => ((i'.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i'.val : ℤ) + u)) A i (z i)
    (fun j : Fin n => (j.val : ℤ) - i.val) (Set.Ico 0 (u : ℤ)) (fun j hj => by simp only [Set.mem_Ico]; omega) (fun j hj => h i j hj)
    (h_uniq i) (h_pad i)
  rw [e1, e2]


-- created on 2022-01-03
