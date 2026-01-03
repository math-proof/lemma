import Lemma.List.EqCons_Tail.of.NeLength_0
import sympy.functions.special.tensor_functions
import sympy.tensor.stack
open List


/--
Identity matrix of size `n x n` as a tensor that mimics the behavior of `torch.eye` or `sympy.Identity`.
- [sympy.Identity](https://github.com/sympy/sympy/blob/master/sympy/matrices/expressions/special.py#L104)
- [torch.eye](https://docs.pytorch.org/docs/stable/generated/torch.eye.html)
-/
def eye [AddMonoidWithOne α] [CharZero α] (n : Nat) : Tensor α [n, n] := [i < n] [j < n] (KroneckerDelta i j)

/--
[masked_fill](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.masked_fill.html)
-/
def Tensor.masked_fill [Zero α] (X : Tensor α s) (d : ℤ) (cmp : ℤ → ℤ → Prop) [DecidableRel cmp]  : Tensor α s :=
  if h_s : s.length > 2 then
    cast
      (by
        rw [HeadD.eq.Get_0.of.NeLength_0 (by linarith)]
        rw [EqCons_Tail.of.NeLength_0 (by linarith)]
      )
      (Tensor.fromVector (X.toVector.map (·.masked_fill d cmp)))
  else if h_s : s.length < 2 then
    X
  else
    have h_s : s.length = 2 := by grind
    match h : s with
    | [m, n] =>
      [i < m] [j < n] (if cmp (j - i) d  then 0 else (X.get ⟨i, by grind⟩).get ⟨j, by grind⟩)

/--
[torch.tril](https://docs.pytorch.org/docs/stable/generated/torch.tril.html)
-/
def Tensor.tril [Zero α] (X : Tensor α s) (diagonal : ℤ) : Tensor α s := X.masked_fill diagonal GT.gt

/--
[torch.triu](https://docs.pytorch.org/docs/stable/generated/torch.triu.html)
-/
def Tensor.triu [Zero α] (X : Tensor α s) (diagonal : ℤ) : Tensor α s := X.masked_fill diagonal LT.lt

/--
dilated version of [band_part](https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part)
-/
def Tensor.band_part [Zero α] (X : Tensor α s) (l : ℕ) (u : ℕ) (d : ℕ := 1) : Tensor α s :=
  ((X.tril u).triu (-l)).masked_fill d (fun Δ d => ¬d ∣ Δ + l)
