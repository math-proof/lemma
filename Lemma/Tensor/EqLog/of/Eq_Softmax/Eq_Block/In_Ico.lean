import Lemma.Tensor.LogGetGetSoftmaxAdd_Mul_Infty.eq.Coe_Z
import sympy.Basic
open Tensor


/--
Hyperreal masked softmax, log form (py: `log(softmax(A + (Ξ - 1) * oo)[i, j])` on the unmasked entries `Ξ i j = 1`).
-/
@[main]
private lemma main
  {n l u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h_l : 0 < l)
  (h_u : 0 < u)
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) →
    let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)))
    let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (((A i j) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
    Log.log (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []) ≈
      (((z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) : ℝ) : Tensor ℝ []) : Tensor ℝ* []) := by
-- proof
  intro i j hp
  exact LogGetGetSoftmaxAdd_Mul_Infty.eq.Coe_Z (n := n) (m := n) (fun i j => ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)) (fun i j => ((A i j) : ℝ)) (fun i j => z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) (fun i => ⟨i, by omega⟩) h i j hp


/--
Hyperreal masked softmax, log form (py: `log(softmax(A + (Ξ - 1) * oo)[i, j])` on the unmasked entries `Ξ i j = 1`).
-/
@[main]
private lemma tf
  {n l u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h_l : 0 < l)
  (h_u : 0 < u)
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) →
    let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)))
    let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (((A i j) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
    Log.log (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []) ≈
      (((z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) : ℝ) : Tensor ℝ []) : Tensor ℝ* []) := by
-- proof
  intro i j hp
  exact LogGetGetSoftmaxAdd_Mul_Infty.eq.Coe_Z (n := n) (m := n) (fun i j => ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)) (fun i j => ((A i j) : ℝ)) (fun i j => z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) (fun i => ⟨i, by omega⟩) h i j hp


/--
Hyperreal masked softmax, log form (py: `log(softmax(A + (Ξ - 1) * oo)[i, j])` on the unmasked entries `Ξ i j = 1`).
-/
@[main]
private lemma upper_triangle
  {n u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h_u : 0 < u)
  (h : ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) ≤ (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) →
    let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)))
    let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (((A i j) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
    Log.log (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []) ≈
      (((z i ((j.val : ℤ) - i.val) : ℝ) : Tensor ℝ []) : Tensor ℝ* []) := by
-- proof
  intro i j hp
  exact LogGetGetSoftmaxAdd_Mul_Infty.eq.Coe_Z (n := n) (m := n) (fun i j => ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)) (fun i j => ((A i j) : ℝ)) (fun i j => z i ((j.val : ℤ) - i.val)) (fun i => ⟨i, by omega⟩) h i j hp


/--
Hyperreal masked softmax, log form (py: `log(softmax(A + (Ξ - 1) * oo)[i, j])` on the unmasked entries `Ξ i j = 1`).
-/
@[main]
private lemma upper_triangle.tf
  {n u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h_u : 0 < u)
  (h : ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) ≤ (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) →
    let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)))
    let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (((A i j) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
    Log.log (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []) ≈
      (((z i ((j.val : ℤ) - i.val) : ℝ) : Tensor ℝ []) : Tensor ℝ* []) := by
-- proof
  intro i j hp
  exact LogGetGetSoftmaxAdd_Mul_Infty.eq.Coe_Z (n := n) (m := n) (fun i j => ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)) (fun i j => ((A i j) : ℝ)) (fun i j => z i ((j.val : ℤ) - i.val)) (fun i => ⟨i, by omega⟩) h i j hp


/--
Hyperreal masked softmax, log form (py: `log(softmax(A + (Ξ - 1) * oo)[i, j])` on the unmasked entries `Ξ i j = 1`).
-/
@[main]
private lemma lower_triangle
  {n l : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h_l : 0 < l)
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) →
    let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val)))
    let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (((A i j) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
    Log.log (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []) ≈
      (((z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) : ℝ) : Tensor ℝ []) : Tensor ℝ* []) := by
-- proof
  intro i j hp
  exact LogGetGetSoftmaxAdd_Mul_Infty.eq.Coe_Z (n := n) (m := n) (fun i j => ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val)) (fun i j => ((A i j) : ℝ)) (fun i j => z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) (fun i => ⟨i, by omega⟩) h i j hp


/--
Hyperreal masked softmax, log form (py: `log(softmax(A + (Ξ - 1) * oo)[i, j])` on the unmasked entries `Ξ i j = 1`).
-/
@[main]
private lemma lower_triangle.tf
  {n l : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h_l : 0 < l)
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) →
    let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val)))
    let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (((A i j) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
    Log.log (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []) ≈
      (((z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) : ℝ) : Tensor ℝ []) : Tensor ℝ* []) := by
-- proof
  intro i j hp
  exact LogGetGetSoftmaxAdd_Mul_Infty.eq.Coe_Z (n := n) (m := n) (fun i j => ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val)) (fun i j => ((A i j) : ℝ)) (fun i j => z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) (fun i => ⟨i, by omega⟩) h i j hp


-- created on 2022-01-05
