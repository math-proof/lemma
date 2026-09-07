import Lemma.List.Append.of.Eq
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.Drop.eq.ListGet.of.GtLength_0
import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.List.ZipWith_Append.eq.AppendZipWithS
import Lemma.List.ZipWith__Append.eq.AppendZipWithS
import sympy.tensor.tensor
open List Tensor


/--
[torch.matmul](https://docs.pytorch.org/docs/stable/generated/torch.matmul.html)

Mirrors [sympy.MatMul](https://github.com/sympy/sympy/blob/master/sympy/matrices/expressions/matmul.py).
-/
def Tensor.matmul [Mul α] [Add α] [Zero α] (X : Tensor α (s ++ [m, t])) (Y : Tensor α (s' ++ [t, k])) (h : s.length = s'.length) : Tensor α (broadcast_shape s s' ++ [m, k]) :=
  match s, s' with
  | [], [] =>
    bmm X Y
  | n :: s, n' :: s' =>
    have h : s.length = s'.length := by grind
    let X : Tensor α (n ⊔ n' :: s ++ [m, t]) := X.resize ⟨0, by grind⟩ (n ⊔ n')
    let Y : Tensor α (n ⊔ n' :: s' ++ [t, k]) := Y.resize ⟨0, by grind⟩ (n ⊔ n')
    cast
      (by
        congr
        simp [broadcast_shape]
        split_ifs
        repeat simp_all
      )
      (OfVector (List.Vector.map₂ (fun X Y => matmul X Y h) X.toVector Y.toVector))

/--
[torch.tensordot](https://docs.pytorch.org/docs/stable/generated/torch.tensordot.html)
-/
def Tensor.tensordot [Mul α] [Add α] [Zero α] (X : Tensor α (s ++ [m, n])) (Y : Tensor α (s' ++ [n, k])) : Tensor α (broadcast_shape s s' ++ [m, k]) :=
  if h : s.length < s'.length then
    let X := X.reshape (s'.take (s'.length - s.length) ++ s ++ [m, n]) (by simp)
    cast (congrArg (Tensor α) (by
      simp [broadcast_shape]
      split_ifs with h_l h_u
      .
        grind
      .
        grind
      .
        simp
        rw [Append_Append.eq.AppendAppend]
        apply Append.of.Eq
        rw [ZipWith_Append.eq.AppendZipWithS]
        apply Append.of.Eq
        simp
    ))
    (matmul X Y (by grind))
  else if h : s.length > s'.length then
    let Y := Y.reshape (s.take (s.length - s'.length) ++ s' ++ [n, k]) (by simp)
    cast (congrArg (Tensor α) (by
      simp [broadcast_shape]
      split_ifs with h_l h_u
      .
        grind
      .
        grind
      .
        simp
        rw [Append_Append.eq.AppendAppend]
        apply Append.of.Eq
        rw [ZipWith__Append.eq.AppendZipWithS]
        apply Append.of.Eq
        simp
    ))
    (matmul X Y (by grind))
  else
    matmul X Y (by grind)

/--
perform matrix multiplication between two tensors like
[torch.einsum](https://docs.pytorch.org/docs/stable/generated/torch.einsum.html)
if the batch dimensions are different, the shorter length is broadcasted to the longer one, eg:
- if A.shape = [1, 4, 5], B.shape = [9, 5, 6], then the result is :
  A.repeat 9 0 @ B,  with shape of [9, 4, 6]
- if A.shape = [3, 4, 5], B.shape = [9, 5, 6], then the result is :
  A.repeat 3 0 @ B,  with shape of [9, 4, 6]
- if A.shape = [2, 4, 5], B.shape = [9, 5, 6], then the result is :
  A.repeat 4 0 ++ (0 : Tensor α [1, 4, 5]) @ B,  with shape of [9, 4, 6]
-- instance [Mul α] [Add α] [Zero α] : MatMul (Tensor α (batch_size ++ [m, k])) (Tensor α (batch_size ++ [k, n])) (Tensor α (batch_size ++ [m, n])) := ⟨dot⟩
-/
def Tensor.einsum [Mul α] [Add α] [Zero α] (X : Tensor α s) (Y : Tensor α s') : Tensor α (matmul_shape s s') :=
  if h_s : s.length = 0 then
    cast (by simp_all [matmul_shape]) (X.data[0]'(by simp_all) * Y)
  else if h_s' : s'.length = 0 then
    cast (by simp_all [matmul_shape]) (X * Y.data[0]'(by simp_all))
  else if h_s : s.length = 1 then
    match s with
    | [n] =>
      if h_s' : s'.length = 1 then
        match s' with
        | [n'] =>
          let X : Tensor α [n ⊔ n'] := X.resize ⟨0, by grind⟩ (n ⊔ n')
          let Y : Tensor α [n ⊔ n'] := Y.resize ⟨0, by grind⟩ (n ⊔ n')
          (X * Y).sum
      else
        have h_s' : s'.length ≥ 2 := by omega
        let batch_size' := s'.take (s'.length - 2)
        let n' := s'[s'.length - 2]
        let k' := s'[s'.length - 1]
        let X : Tensor α [n ⊔ n'] := X.resize ⟨0, by grind⟩ (n ⊔ n')
        let X := X.reshape ((batch_size' ++ [1, n ⊔ n'])) (by simp)
        let Y : Tensor α (batch_size' ++ [n', k']) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) Y
        let Y : Tensor α (batch_size' ++ [n ⊔ n', k']) := cast (congrArg (Tensor α) (by simp)) (Y.resize ⟨batch_size'.length, by grind⟩ (n ⊔ n'))
        cast
          (by
            congr
            simp [batch_size', k', matmul_shape]
            have h_s' : s' ≠ [] := by grind
            simp [h_s']
            rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
            simp [EraseIdx.eq.Append_Drop_Add_1]
            simp [show s'.length - 2 + 1 = s'.length - 1 by omega]
            rw [Drop.eq.ListGet.of.GtLength_0 (by omega)]
          )
          ((X.bmm Y).select ⟨s'.length - 2, by simp [batch_size']⟩ ⟨0, by grind⟩)
  else if h_s' : s'.length = 1 then
    match s' with
    | [n'] =>
      have h_s : s.length ≥ 2 := by omega
      let batch_size := s.take (s.length - 2)
      let k := s[s.length - 2]
      let n := s[s.length - 1]
      let X : Tensor α (batch_size ++ [k, n]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) X
      let X : Tensor α (batch_size ++ [k, n ⊔ n']) := cast (congrArg (Tensor α) (by simp)) (X.resize ⟨batch_size.length + 1, by grind⟩ (n ⊔ n'))
      let Y : Tensor α [n ⊔ n'] := Y.resize ⟨0, by grind⟩ (n ⊔ n')
      let Y := Y.reshape ((batch_size ++ [n ⊔ n', 1])) (by simp)
      cast
        (by
          congr
          simp [batch_size, k, matmul_shape]
          have h_s : s ≠ [] := by grind
          simp [h_s]
          have h_s : s.length ≠ 1 := by grind
          simp [h_s]
          rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
          simp [EraseIdx.eq.Append_Drop_Add_1]
          simp [show s.length - 1 - (s.length - 2) = 1 by omega]
          simp [show s.length - 2 + 1 = s.length - 1 by omega]
          rw [DropLast.eq.Take_SubLength_1]
        )
        ((X.bmm Y).select ⟨s.length - 1, by simp [batch_size]; omega⟩ ⟨0, by grind⟩)
  else
    have h_s : s.length ≥ 2 := by omega
    have h_s' : s'.length ≥ 2 := by omega
    let batch_size := s.take (s.length - 2)
    let batch_size' := s'.take (s'.length - 2)
    let m := s[s.length - 2]
    let n := s[s.length - 1]
    let n' := s'[s'.length - 2]
    let k := s'[s'.length - 1]
    let X : Tensor α (batch_size ++ [m, n]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) X
    let X : Tensor α (batch_size ++ [m, n ⊔ n']) := cast (congrArg (Tensor α) (by simp)) (X.resize ⟨batch_size.length + 1, by grind⟩ (n ⊔ n'))
    let Y : Tensor α (batch_size' ++ [n', k]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) Y
    let Y : Tensor α (batch_size' ++ [n ⊔ n', k]) := cast (congrArg (Tensor α) (by simp)) (Y.resize ⟨batch_size'.length, by grind⟩ (n ⊔ n'))
    cast
      (by
        congr
        simp [batch_size, batch_size', m, k, matmul_shape, broadcast_shape]
        grind
      )
      (tensordot X Y)

/--
Tensor matrix product (`@`).
-/
instance [Mul α] [Add α] [Zero α] : Dot (Tensor α s) (Tensor α s') (Tensor α (matmul_shape s s')) := ⟨einsum⟩
