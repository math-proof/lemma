module

public import Def.Data.Tensor.Defs.Part4
public import Def.Data.List.List.Basic
public import Def.Data.Tensor.Resize
public import Def.Data.Tensor.Shape
public import Def.Data.Tensor.Sum
public import Def.Data.Tensor.Mean
public import Def.Data.Tensor.Bmm
public import Def.Data.Tensor.Prod
public import Def.Data.Tensor.Reshape
public import Def.Data.Tensor.Unsqueeze
public import Def.Data.Tensor.Repeat
public import Notation.Data.Tensor.Permute
public import Def.Data.Tensor.Item
public import Def.Data.Tensor.HStack
public import Theorem.Bool.HEq.of.All_HEq
public import Theorem.Nat.Le_Sub_1.of.Lt
public import Theorem.Nat.LtAddS.is.Lt
public import Theorem.List.MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq
public import Theorem.List.HeadD.eq.Get_0.of.GtLength_0
public import Theorem.List.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
public import Theorem.List.GtLength_0.of.Cons.in.CartesianProduct
public import Theorem.List.EqCons_Tail.of.GtLength_0
public import Theorem.List.LengthTake.gt.Zero.of.LengthTake.gt.Zero
public import Theorem.List.In_CartesianProduct.of.In_CartesianProductCons
public import Theorem.List.Lt.of.In_CartesianProductCons
public import Theorem.Tensor.Length.eq.Get_0.of.GtLength_0
public import Theorem.Tensor.GtLength_0.of.GtLength_0
public import Theorem.Tensor.Length.eq.Get_0.of.GtLength
public import Def.Data.Tensor.Tensor
public import Theorem.Nat.MulMul.eq.Mul_Mul
@[expose] public section
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
    have h_in : index :: indices ∈ (s[0] :: s.tail.take indices.length).cartesianProduct := by rwa [← EqCons_Tail.of.GtLength_0 h_pos] at h
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
    (X.get i).data
  ⟨cast (by simp) tensors.flatten⟩

/-- Infoview: reverse `getSlice` to Python/PyTorch slice syntax. -/
@[app_unexpander Tensor.getSlice]
meta def Tensor.getSlice.unexpand := Slice.getSliceUnexpand

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
          let ti : Tensor α (s.drop 1) := ⟨(X.get ⟨i.val, this⟩).data.val, by simp⟩
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
              rw [LtAddS.is.Lt]
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
            simp [← MulMul.eq.Mul_Mul]
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

