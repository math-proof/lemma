import sympy.tensor.Basic
import Lemma.Bool.HEq.of.All_HEq
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.GtVal_0.of.Ne_0
import Lemma.Nat.LtSubS_1.of.Lt.Ne_0
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqAddMulDiv
import Lemma.Int.LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
import Lemma.List.Drop.eq.ListGetS.of.GeLength_2
import Lemma.List.ZipWith_AppendS.eq.AppendZipWithS
import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.List.MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
import Lemma.List.GtLength_0.of.Cons.in.CartesianProduct
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.LengthTake.gt.Zero.of.LengthTake.gt.Zero
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.Sub_1.lt.LengthTail.of.In_Ioo0Length
import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.In_CartesianProduct.of.In_CartesianProductCons
import Lemma.List.Lt.of.In_CartesianProductCons
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GtLength_0.of.GtLength_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.DataInv.eq.InvData
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength
-- @[grind =]
import Lemma.Tensor.EqLength
import Lemma.Tensor.LengthMap.eq.Length
open Bool Nat Int List Tensor

def Tensor.get (X : Tensor α s) (i : Fin X.length) : Tensor α s.tail :=
  have h_i := i.isLt
  have h_GtLength_0 := GtLength_0.of.GtLength_0 (X := X) (by linarith)
  have h_EqHeadD := HeadD.eq.Get_0.of.GtLength_0 h_GtLength_0 1
  have := Get_0.eq.Length.of.GtLength_0 h_GtLength_0 X
  X.toVector[i]

/--
[torch.select](https://docs.pytorch.org/docs/stable/generated/torch.select.html)
-/
def Tensor.select (X : Tensor α s) (offset : Fin s.length) (i : Fin s[offset])  : Tensor α (s.eraseIdx offset) :=
  have h_s_length := Gt_0 offset
  if h : offset = ⟨0, h_s_length⟩ then
    cast
      (by
        substs h
        simp
      )
      (X.get ⟨i, by
        have h_i := i.isLt
        simp [h] at h_i
        rwa [Length.eq.Get_0.of.GtLength_0 h_s_length]
      ⟩)
  else
    have h := GtVal_0.of.Ne_0 h
    have h_lt := LtSubS_1.of.Lt.Ne_0 (by linarith) (by simp) (n := offset) (m := s.length)
    have h_1 := Ge_1.of.Gt_0 h
    have X : Tensor α (s.headD 1 :: s.tail.eraseIdx (offset - 1)) := Tensor.fromVector (
      X.toVector.map (
        ·.select
          ⟨offset - 1, Sub_1.lt.LengthTail.of.In_Ioo0Length ⟨h, by simp⟩⟩
          ⟨i, by
            simp only [GetElem.getElem]
            rw [GetTail.eq.Get_Add_1.of.Lt_SubLength_1.fin]
            simp [EqAddSub.of.Ge h_1]
            assumption
          ⟩
      )
    )
    cast
      (by
        rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 (by assumption)]
        simp only [EqAddSub.of.Ge h_1]
        conv_rhs =>
          rw [Eq_Cons_Tail.of.GtLength_0 (show (s.eraseIdx offset).length > 0 by grind)]
        congr
        rw [GetEraseIdx.eq.Get.of.Gt.GtLength]
        · apply List.HeadD.eq.Get_0.of.GtLength_0
        · simp
        · assumption
      )
      X

def Tensor.broadcast_matmul_rec [Mul α] [Add α] [Zero α] (X : Tensor α (s ++ [m, t])) (Y : Tensor α (s' ++ [t, k])) (h : s.length = s'.length) : Tensor α (Tensor.broadcast_shape s s' ++ [m, k]) :=
  match s, s' with
  | [], [] =>
    Tensor.batch_dot X Y
  | n :: s, n' :: s' =>
    have h : s.length = s'.length := by grind
    let ⟨X, Y⟩ : Tensor α (n ⊔ n' :: s ++ [m, t]) × Tensor α (n ⊔ n' :: s' ++ [t, k]) :=
      if h_n : n < n' then
        let q := n' / n
        let r := n' % n
        let X : Tensor α (n' :: s ++ [m, t]) := cast
          (by simp [q, r, EqAddMulDiv])
          ((cast (by simp_all) (X.repeat q ⟨0, by simp⟩) : Tensor α (q * n :: (s ++ [m, t]))) ++ (0 : Tensor α (r :: (s ++ [m, t]))))
        ⟨cast (by grind) X, cast (by grind) Y⟩
      else if h_n : n > n' then
        let q := n / n'
        let r := n % n'
        let Y : Tensor α (n :: s' ++ [t, k]) := cast
          (by simp [q, r, EqAddMulDiv])
          ((cast (by simp_all) (Y.repeat q ⟨0, by simp⟩) : Tensor α (q * n' :: (s' ++ [t, k]))) ++ (0 : Tensor α (r :: (s' ++ [t, k]))))
        ⟨cast (by grind) X, cast (by grind) Y⟩
      else
        ⟨cast (by grind) X, cast (by grind) Y⟩
    cast
      (by
        congr
        simp [broadcast_shape]
        split_ifs
        repeat simp_all
      )
      (Tensor.fromVector (List.Vector.map₂ (fun x y => broadcast_matmul_rec x y h) X.toVector Y.toVector))

def Tensor.broadcast_matmul [Mul α] [Add α] [Zero α] (X : Tensor α (s ++ [m, n])) (Y : Tensor α (s' ++ [n, k])) : Tensor α (Tensor.broadcast_shape s s' ++ [m, k]) :=
  if h : s.length < s'.length then
    let X := X.broadcast (s'.take (s'.length - s.length) ++ s ++ [m, n]) (by simp)
    cast
      (by
        apply congrArg
        simp [broadcast_shape]
        split_ifs with h_l h_u
        .
          grind
        .
          grind
        .
          simp
          rw [Append_Append.eq.AppendAppend]
          apply EqAppendS.of.Eq
          have h_s := EqAppendTake__Drop s' (s'.length - s.length)
          conv_lhs =>
            arg 3
            rw [← h_s]
          rw [ZipWith_AppendS.eq.AppendZipWithS (by rfl)]
          apply EqAppendS.of.Eq
          simp
      )
      (broadcast_matmul_rec X Y (by grind))
  else if h : s.length > s'.length then
    let Y := Y.broadcast (s.take (s.length - s'.length) ++ s' ++ [n, k]) (by simp)
    cast
      (by
        apply congrArg
        simp [broadcast_shape]
        split_ifs with h_l h_u
        .
          grind
        .
          grind
        .
          simp
          rw [Append_Append.eq.AppendAppend]
          apply EqAppendS.of.Eq
          have h_s := EqAppendTake__Drop s (s.length - s'.length)
          conv_lhs =>
            arg 2
            rw [← h_s]
          rw [ZipWith_AppendS.eq.AppendZipWithS (by rfl)]
          apply EqAppendS.of.Eq
          simp
      )
      (broadcast_matmul_rec X Y (by grind))
  else
    broadcast_matmul_rec X Y (by grind)

/--
perform matrix multiplication between two tensors like
[torch.matmul](https://docs.pytorch.org/docs/stable/generated/torch.matmul.html)
if the batch dimensions are different, the shorter length is broadcasted to the longer one, eg:
- if A.shape = [1, 4, 5], B.shape = [9, 5, 6], then the result is :
  A.repeat 9 0 @ B,  with shape of [9, 4, 6]
- if A.shape = [3, 4, 5], B.shape = [9, 5, 6], then the result is :
  A.repeat 3 0 @ B,  with shape of [9, 4, 6]
- if A.shape = [2, 4, 5], B.shape = [9, 5, 6], then the result is :
  A.repeat 4 0 ++ (0 : Tensor α [1, 4, 5]) @ B,  with shape of [9, 4, 6]
-- instance [Mul α] [Add α] [Zero α] : MatMul (Tensor α (batch_size ++ [m, k])) (Tensor α (batch_size ++ [k, n])) (Tensor α (batch_size ++ [m, n])) := ⟨Tensor.dot⟩
-/
def Tensor.matmul [Mul α] [Add α] [Zero α] (X : Tensor α s) (Y : Tensor α s') : Tensor α (Tensor.matmul_shape s s') :=
  if h_s : s.length = 0 then
    cast (by simp_all [Tensor.matmul_shape]) (Y.map (fun y => X.data[0]'(by simp_all) * y))
  else if h_s' : s'.length = 0 then
    cast (by simp_all [Tensor.matmul_shape]) (X.map (fun x => x * Y.data[0]'(by simp_all)))
  else if h_s : s.length = 1 then
    match s with
    | [n] =>
      if h_s' : s'.length = 1 then
        match s' with
        | [n'] =>
          let ⟨X, Y⟩ : Tensor α [n ⊔ n'] × Tensor α [n ⊔ n'] :=
            if h_n : n < n' then
              let q := n' / n
              let r := n' % n
              let X : Tensor α [n'] := cast
                (by simp [q, r, EqAddMulDiv])
                ((cast (by simp_all) (X.repeat q ⟨0, by linarith⟩) : Tensor α [q * n]) ++ (0 : Tensor α [r]))
              ⟨cast (by grind) X, cast (by grind) Y⟩
            else if h_n : n > n' then
              let q := n / n'
              let r := n % n'
              let Y : Tensor α [n] := cast
                (by simp [q, r, EqAddMulDiv])
                ((cast (by simp_all) (Y.repeat q ⟨0, by linarith⟩) : Tensor α [q * n']) ++ (0 : Tensor α [r]))
              ⟨cast (by grind) X, cast (by grind) Y⟩
            else
              ⟨cast (by grind) X, cast (by grind) Y⟩
          ((X.data * Y.data).sum : Tensor α [])
      else
        have h_s' : s'.length ≥ 2 := by omega
        let batch_size' := s'.take (s'.length - 2)
        let n' := s'[s'.length - 2]
        let k' := s'[s'.length - 1]
        let Y : Tensor α (batch_size' ++ [n', k']) := cast
          (by
            congr
            simp [batch_size', n', k']
            conv_lhs => rw [← EqAppendTake__Drop s' (s'.length - 2)]
            apply EqAppendS.of.Eq.left
            apply Drop.eq.ListGetS.of.GeLength_2 h_s'
          )
          Y
        let ⟨X, Y⟩ : Tensor α [n ⊔ n'] × Tensor α (batch_size' ++ [n ⊔ n', k']) :=
          if h_n : n < n' then
            let q := n' / n
            let r := n' % n
            let X : Tensor α [n'] := cast
              (by simp [q, r, EqAddMulDiv])
              ((cast (by grind) (X.repeat q ⟨0, by linarith⟩) : Tensor α [q * n]) ++ (0 : Tensor α [r]))
            ⟨cast (by grind) X, cast (by grind) Y⟩
          else if h_n : n > n' then
            let q := n / n'
            let r := n % n'
            let Y : Tensor α (batch_size' ++ [n, k']) := cast (by simp [q, r, EqAddMulDiv]) ((cast (by simp [batch_size']) (Y.repeat q ⟨s'.length - 2, by simp [batch_size']⟩) : Tensor α (batch_size' ++ [q * n', k'])) ++ (0 : Tensor α (batch_size' ++ [r, k'])))
            ⟨cast (by grind) X, cast (by grind) Y⟩
          else
            ⟨cast (by grind) X, cast (by grind) Y⟩
        let X := X.broadcast ((batch_size' ++ [1, n ⊔ n'])) (by simp)
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
          ((X.batch_dot Y).select ⟨s'.length - 2, by simp [batch_size']⟩ ⟨0, by grind⟩)
  else if h_s' : s'.length = 1 then
    match s' with
    | [n'] =>
      have h_s : s.length ≥ 2 := by omega
      let batch_size := s.take (s.length - 2)
      let k := s[s.length - 2]
      let n := s[s.length - 1]
      let X : Tensor α (batch_size ++ [k, n]) := cast
        (by
          congr
          simp [batch_size, n, k]
          conv_lhs => rw [← EqAppendTake__Drop s (s.length - 2)]
          apply EqAppendS.of.Eq.left
          apply Drop.eq.ListGetS.of.GeLength_2 h_s
        )
        X
      let ⟨X, Y⟩ : Tensor α (batch_size ++ [k, n ⊔ n']) × Tensor α [n ⊔ n'] :=
        if h_n : n < n' then
          let q := n' / n
          let r := n' % n
          let X : Tensor α (batch_size ++ [k, n']) := cast (by simp [q, r, EqAddMulDiv]) ((cast (by simp [batch_size]; grind) (X.repeat q ⟨s.length - 1, by simp [batch_size]; omega⟩) : Tensor α (batch_size ++ [k] ++ [q * n])) ++ (0 : Tensor α (batch_size ++ [k] ++ [r])))
          ⟨cast (by grind) X, cast (by grind) Y⟩
        else if h_n : n > n' then
          let q := n / n'
          let r := n % n'
          let Y : Tensor α [n] := cast
            (by simp [q, r, EqAddMulDiv])
            ((cast (by grind) (Y.repeat q ⟨0, by linarith⟩) : Tensor α [q * n']) ++ (0 : Tensor α [r]))
          ⟨cast (by grind) X, cast (by grind) Y⟩
        else
          ⟨cast (by grind) X, cast (by grind) Y⟩
      let Y := Y.broadcast ((batch_size ++ [n ⊔ n', 1])) (by simp)
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
        ((X.batch_dot Y).select ⟨s.length - 1, by simp [batch_size]; omega⟩ ⟨0, by grind⟩)
  else
    have h_s : s.length ≥ 2 := by omega
    have h_s' : s'.length ≥ 2 := by omega
    let batch_size := s.take (s.length - 2)
    let batch_size' := s'.take (s'.length - 2)
    let m := s[s.length - 2]
    let n := s[s.length - 1]
    let n' := s'[s'.length - 2]
    let k := s'[s'.length - 1]
    let X : Tensor α (batch_size ++ [m, n]) := cast
      (by
        congr
        simp [batch_size, m, n]
        conv_lhs => rw [← EqAppendTake__Drop s (s.length - 2)]
        apply EqAppendS.of.Eq.left
        apply Drop.eq.ListGetS.of.GeLength_2 h_s
      )
      X
    let Y : Tensor α (batch_size' ++ [n', k]) := cast
      (by
        congr
        simp [batch_size', n', k]
        conv_lhs => rw [← EqAppendTake__Drop s' (s'.length - 2)]
        apply EqAppendS.of.Eq.left
        apply Drop.eq.ListGetS.of.GeLength_2 h_s'
      )
      Y
    let ⟨X, Y⟩ : Tensor α (batch_size ++ [m, n ⊔ n']) × Tensor α (batch_size' ++ [n ⊔ n', k]) :=
      if h_n : n < n' then
        let q := n' / n
        let r := n' % n
        let X : Tensor α (batch_size ++ [m, n']) := cast
          (by simp [q, r, EqAddMulDiv])
          ((cast (by simp; grind) (X.repeat q ⟨s.length - 1, by simp [batch_size]; omega⟩) : Tensor α (batch_size ++ [m] ++ [q * n])) ++ (0 : Tensor α (batch_size ++ [m] ++ [r])))
        ⟨cast (by grind) X, cast (by grind) Y⟩
      else if h_n : n > n' then
        let q := n / n'
        let r := n % n'
        let Y : Tensor α (batch_size' ++ [n, k]) := cast
          (by simp [q, r, EqAddMulDiv])
          ((cast (by simp [batch_size']) (Y.repeat q ⟨s'.length - 2, by simp [batch_size']⟩) : Tensor α (batch_size' ++ [q * n', k])) ++ (0 : Tensor α (batch_size' ++ [r, k])))
        ⟨cast (by grind) X, cast (by grind) Y⟩
      else
        ⟨cast (by grind) X, cast (by grind) Y⟩
    cast
      (by
        congr
        simp [batch_size, batch_size', m, k, matmul_shape, broadcast_shape]
        grind
      )
      (broadcast_matmul X Y)

instance [Mul α] [Add α] [Zero α] : MatMul (Tensor α s) (Tensor α s') (Tensor α (Tensor.matmul_shape s s')) := ⟨Tensor.matmul⟩

instance [Mul α] [Add α] [Zero α] : MatMul (Tensor α [m, k]) (Tensor α [k, n]) (Tensor α [m, n]) where
  dot A B :=
    let A : Tensor α ([] ++ [m, k]) := A
    A.batch_dot B

instance : GetElem (Tensor α s) ℕ (Tensor α s.tail) fun X i => i < X.length where
  getElem X i h := X.get ⟨i, h⟩

instance : GetElem (Tensor α s) ℤ (Tensor α s.tail) fun X i => i ∈ Ico (-X.length : ℤ) X.length where
  getElem X i h :=
    have := LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg h
    let i := Slice.Add_Mul_DivSub1Sign_2 X.length i
    X[i.toNat]

instance : GetElem (Tensor α s) (Tensor ℕ []) (Tensor α s.tail) fun X i => i.data[0] < X.length where
  getElem X i h := X[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℤ []) (Tensor α s.tail) fun X i => i.data[0] ∈ Ico (-X.length : ℤ) X.length where
  getElem X i _ := X[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℕ [n].tail) (Tensor α s.tail) fun X i => i.data[0] < X.length where
  getElem X i _ := X[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℤ [n].tail) (Tensor α s.tail) fun X i => i.data[0] ∈ Ico (-X.length : ℤ) X.length where
  getElem X i _ := X[i.data[0]]

instance : GetElem (Tensor α (m :: s)) (Tensor (Fin k) [n].tail) (Tensor α s) fun _ _ => k ≤ m where
  getElem X i h := X[i.data[0]]

/--
Represents a mathematical object with indices.
X[i, j, k].shape = X.shape.drop 3
-/
def Tensor.getElem (base : Tensor α s) (indices : List ℕ) (h : indices ∈ (s.take indices.length).cartesianProduct) : Tensor α (s.drop indices.length) :=
  match indices with
  | .nil =>
    base
  | index :: indices =>
    have h_pos := GtLength_0.of.Cons.in.CartesianProduct h
    have h_pos := LengthTake.gt.Zero.of.LengthTake.gt.Zero h_pos
    have h_in : index :: indices ∈ (s[0] :: s.tail.take indices.length).cartesianProduct := by rwa [Eq_Cons_Tail.of.GtLength_0 h_pos] at h
    have h := In_CartesianProduct.of.In_CartesianProductCons h_in
    have := Lt.of.In_CartesianProductCons h_in
    cast (by simp) (getElem (base.get ⟨index, by rwa [Length.eq.Get_0.of.GtLength_0 h_pos base]⟩) indices h)

/--
mimics tensor slicing in libraries like PyTorch: X[start:stop:step]
-/
def Tensor.getSlice
  (X : Tensor α s)
  (slice : Slice) :
  Tensor α (slice.length X.length :: s.tail) :=
  let tensors := (List.Vector.indices slice X.length).map fun i =>
    X[i].data
  ⟨cast (by simp) tensors.flatten⟩

def Tensor.getSlices
  (X : Tensor α s)
  (slices : List Slice)
  {h_shape : slices.length ≤ s.length} :
  Tensor α ((slices.enumerate.map fun ⟨i, index⟩ => index.length s[i]) ++ s.drop slices.length) :=
  match h_slice : slices with
  | .nil =>
    X
  | index :: slices =>
    match h_slices : slices with
    | .nil =>
      have := Length.eq.Get_0.of.GtLength_0 (s := s) (by simpa [h_shape]) X
      have : (index.length X.length :: s.tail).prod = (index.length s[0] :: List.drop 1 s).prod := by
        simp_all
      (⟨cast (by rw [this]) (X.getSlice index).data⟩ : Tensor α (index.length s[0] :: s.drop 1))
    | slices'h :: slices't =>
      have h_shape : s.length ≥ (index :: slices).length:= by
        simp_all
      have : s.length > slices.length := by
        simp_all
        linarith
      have : (s.drop 1).length ≥ slices.length:= by
        simp
        apply Le_Sub_1.of.Lt
        assumption
      let shape := slices.enumerate.map fun ⟨i, index⟩ => index.length (s.drop 1)[i]
      let s_rest := (s.drop 1).drop slices.length
      let indices :
        List.Vector (Fin s[0]) (index.length s[0]) :=
        List.Vector.indices index s[0]
      let tensors :
        List.Vector (List.Vector α (shape.prod * s_rest.prod)) (index.length s[0]) :=
        indices.map fun i : Fin s[0] =>
          have : i < X.length := by
            simp_all [Length.eq.Get_0.of.GtLength (by assumption) X]
          let ti : Tensor α (s.drop 1) := ⟨X[i].data.val, by simp⟩
          have h_shape : slices.length ≤ (s.drop 1).length := LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1 (by simp_all) h_shape
          let sliced : Tensor α (shape ++ s_rest) := getSlices ti slices (h_shape := h_shape)
          have h_eq : (shape ++ s_rest).prod = shape.prod * s_rest.prod := by
            simp
          cast (by rw [h_eq]) sliced.data
      have h_cons : index.length s[0] :: shape = (index :: slices).enumerate.map (fun ⟨i, index⟩ => index.length s[i]) := by
        simp [shape]
        let g := fun x : Fin slices.length × Slice => x.2.length s[x.1.val + 1]
        let f := fun x : Fin (slices.length + 1) × Slice => x.2.length s[x.1]
        have h_all : ∀ (i: Fin slices.length) (a : Slice), f ⟨
            ⟨i + 1, by
              apply LtAddS.of.Lt
              simp
            ⟩,
            a
          ⟩ = g ⟨i, a⟩ := by
          intro i a
          simp [f]
          simp [g]
        have := MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq h_all index
        simp [f] at this
        rw [this]
      have h_prod : index.length s[0] * shape.prod = ((index :: slices).enumerate.map (fun ⟨i, index⟩ => index.length s[i])).prod := by
        rw [← h_cons]
        simp
      have h_length : slices.length = slices't.length + 1 := by
        rw [h_slices]
        simp_all
      ⟨
        cast (by
            simp [Mul_Mul.eq.MulMul]
            rw [h_prod]
            simp [← h_length]
            congr
            .
              apply HEq.of.All_HEq
              .
                intros
                congr <;>
                  simp_all
              .
                simp_all
            .
              simp [s_rest]
              rw [add_comm]
          )
          tensors.flatten
      ⟩

instance [AddSemigroup α] : AddSemigroup (Tensor α s) where
  add_assoc a b c := by
    apply Eq.of.EqDataS
    repeat rw [DataAdd.eq.AddDataS]
    apply add_assoc

instance [AddZeroClass α] : AddZeroClass (Tensor α s) where
  zero_add X := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    simp [EqData0'0]
  add_zero X := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    simp [EqData0'0]

instance [MulZeroClass α] : MulZeroClass (Tensor α s) where
  zero_mul X := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS]
    simp [EqData0'0]
  mul_zero X := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS]
    simp [EqData0'0]

instance [AddCommMagma α] : AddCommMagma (Tensor α s) where
  add_comm X Y := by
    apply Eq.of.EqDataS
    repeat rw [DataAdd.eq.AddDataS]
    apply add_comm

instance [AddMonoid α] : AddMonoid (Tensor α s) where
  zero_add
  add_zero
  nsmul n X := ⟨n • X.data⟩
  nsmul_zero X := by
    apply Eq.of.EqDataS
    apply AddMonoid.nsmul_zero
  nsmul_succ n X := by
    apply Eq.of.EqDataS
    apply AddMonoid.nsmul_succ

instance [AddCommSemigroup α] : AddCommSemigroup (Tensor α n) where
  add_comm

instance [AddCommMonoid α] : AddCommMonoid (Tensor α s) where
  zero_add
  add_zero
  add_comm
  nsmul := AddMonoid.nsmul
  nsmul_zero := AddMonoid.nsmul_zero
  nsmul_succ := AddMonoid.nsmul_succ

instance [Mul α] [Add α] [LeftDistribClass α]: LeftDistribClass (Tensor α n) where
  left_distrib A B C := by
    apply Eq.of.EqDataS
    repeat rw [DataAdd.eq.AddDataS]
    repeat rw [DataMul.eq.MulDataS]
    rw [DataAdd.eq.AddDataS]
    apply left_distrib

instance [Mul α] [Add α] [RightDistribClass α]: RightDistribClass (Tensor α n) where
  right_distrib A B C := by
    apply Eq.of.EqDataS
    repeat rw [DataAdd.eq.AddDataS]
    repeat rw [DataMul.eq.MulDataS]
    rw [DataAdd.eq.AddDataS]
    apply right_distrib

instance [Distrib α] : Distrib (Tensor α s) where
  left_distrib
  right_distrib

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Tensor α s) where
  zero_mul
  mul_zero
  left_distrib
  right_distrib

instance [Semigroup α] : Semigroup (Tensor α s) where
  mul_assoc A B C := by
    apply Eq.of.EqDataS
    repeat rw [DataMul.eq.MulDataS]
    apply mul_assoc

instance [SemigroupWithZero α] : SemigroupWithZero (Tensor α s) where
  mul_assoc
  zero_mul
  mul_zero

instance [NonUnitalSemiring α] : NonUnitalSemiring (Tensor α s) where
  mul_assoc

instance [MulOneClass α] : MulOneClass (Tensor α s) where
  one_mul a := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS]
    apply one_mul
  mul_one a := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS]
    apply mul_one

instance [MulZeroOneClass α] : MulZeroOneClass (Tensor α s) where
  one_mul
  mul_one
  zero_mul
  mul_zero

instance [NatCast α] : NatCast (Tensor α n) where
  natCast a := ⟨NatCast.natCast a⟩

instance [AddMonoidWithOne α] : AddMonoidWithOne (Tensor α s) where
  natCast_zero := by
    simp [NatCast.natCast]
    rfl
  natCast_succ a := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    apply AddMonoidWithOne.natCast_succ

instance [AddCommMonoidWithOne α] : AddCommMonoidWithOne (Tensor α s) where
  add_comm

instance [NonAssocSemiring α] : NonAssocSemiring (Tensor α s) where
  one_mul
  mul_one
  zero_mul
  mul_zero
  left_distrib
  right_distrib
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ

instance [MonoidWithZero α] : MonoidWithZero (Tensor α s) where
  one_mul
  mul_one
  zero_mul
  mul_zero

instance [Semiring α] : Semiring (Tensor α s) where
  one_mul
  mul_one
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ

instance [Monoid α] : Monoid (Tensor α s) where
  one_mul
  mul_one

instance [SubNegMonoid α] : SubNegMonoid (Tensor α s) where
  zsmul n v := ⟨n • v.data⟩
  zsmul_zero' x := by
    apply Eq.of.EqDataS
    simp
    rfl
  zsmul_succ' n x := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    simp
    have h := SubNegMonoid.zsmul_succ' n x.data
    simp at h
    assumption
  zsmul_neg' n x := by
    apply Eq.of.EqDataS
    rw [DataNeg.eq.NegData]
    simp
    have h := SubNegMonoid.zsmul_neg' n x.data
    simp at h
    rw [h]

instance [AddGroup α] : AddGroup (Tensor α s) where
  neg_add_cancel x := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    rw [DataNeg.eq.NegData]
    simp [EqData0'0]

instance [DivInvMonoid α] : DivInvMonoid (Tensor α s) where
  div_eq_mul_inv a b := by
    apply Eq.of.EqDataS
    rw [DataDiv.eq.DivDataS]
    rw [DataMul.eq.MulDataS]
    rw [DataInv.eq.InvData]
    rw [DivInvMonoid.div_eq_mul_inv]

instance [NNRatCast α] : NNRatCast (Tensor α s) where
  nnratCast q := ⟨NNRatCast.nnratCast q⟩

instance [NeZero s.prod] [Nontrivial α] : Nontrivial (Tensor α s) where
  exists_pair_ne := by
    let ⟨a, b, h_eq⟩ := Nontrivial.exists_pair_ne (α := List.Vector α s.prod)
    use ⟨a⟩, ⟨b⟩
    simp_all
