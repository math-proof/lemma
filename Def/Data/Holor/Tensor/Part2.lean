import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Select
import Def.Data.Holor.Resize
import Def.Data.Holor.Shape
import Def.Data.Holor.Sum
import Def.Data.Holor.Mean
import Def.Data.Holor.Bmm
import Def.Data.Holor.Prod
import Def.Data.Holor.Reshape
import Def.Data.Holor.Unsqueeze
import Def.Data.Holor.Repeat
import Notation.Data.Holor.Permute
import Def.Data.Holor.Item
import Def.Data.Holor.HStack
import Lemma.Bool.HEq.of.All_HEq
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.GtVal_0.of.Ne_0
import Lemma.Nat.LtSubS_1.of.Lt.Ne_0
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqAddMulDiv
import Lemma.Int.LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
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
import Lemma.Tensor.EqLength
import Lemma.Tensor.LengthMap.eq.Length
import Lemma.Tensor.Eq.is.Item
import Instance.Data.Holor.Tensor
open Bool Nat Int List Tensor


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

/-- Infoview: reverse `getSlice` to Python/PyTorch slice syntax. -/
@[app_unexpander Tensor.getSlice]
def Tensor.getSlice.unexpand := Slice.getSliceUnexpand

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
        aesop
      (⟨cast (by rw [this]) (X.getSlice index).data⟩ : Tensor α (index.length s[0] :: s.drop 1))
    | slices'h :: slices't =>
      have h_shape : s.length ≥ (index :: slices).length:= by
        aesop
      have : s.length > slices.length := by
        aesop
      have : (s.drop 1).length ≥ slices.length:= by
        simp
        apply Le_Sub_1.of.Lt this
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

