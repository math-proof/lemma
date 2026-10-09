import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import torch.linalg
open Tensor


private lemma strip
  [Zero α]
  {n m : ℕ}
  (Y : Tensor α [n, m])
  (k : ℕ) :
  Y.masked_fill 1 (fun Δ d => ¬d ∣ Δ + k) = Y := by
  simp [Tensor.masked_fill]
  apply Eq.of.All_EqGetS.fin
  intro i
  rw [EqGetStack.fin]
  apply Eq.of.All_EqGetS.fin
  intro j
  exact EqGetStack.fin _ j


private lemma triu_eq
  [Zero α]
  {n m : ℕ}
  (Y : Tensor α [n, m])
  {d d' : ℤ}
  (h : ∀ (i : Fin n) (j : Fin m), (j : ℤ) - i < d ↔ (j : ℤ) - i < d') :
  Y.triu d = Y.triu d' := by
  unfold Tensor.triu
  simp [Tensor.masked_fill]
  apply Eq.of.All_EqGetS.fin
  intro i
  rw [EqGetStack.fin]
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_lhs => rw [EqGetStack.fin]
  conv_rhs =>
    rw [EqGetStack.fin]
    rw [EqGetStack.fin]
  split_ifs with h₁
  · erw [if_pos h₁, if_pos ((h i j).mp h₁)]
  · erw [if_neg h₁, if_neg (fun h₂ => h₁ ((h i j).mpr h₂))]


@[path]
private lemma main
  [Zero α]
-- given
  (n m l u : ℕ)
  (X : Tensor α [n, m]) :
-- imply
  X.band_part l u = X.band_part (min l (n - 1)) u := by
-- proof
  unfold Tensor.band_part
  erw [strip _ l, strip _ (min l (n - 1))]
  apply triu_eq (X.tril u)
  intro i j
  have hb : -((n : ℤ) - 1) ≤ (j : ℤ) - i := by omega
  constructor
  · intro hlt
    if h : l ≤ n - 1 then
      simpa [Nat.cast_min, h] using hlt
    else
      omega
  · intro hlt
    if h : l ≤ n - 1 then
      simpa [Nat.cast_min, h] using hlt
    else
      omega


-- created on 2022-01-01
-- updated on 2022-01-23
