import stdlib.List.Vector
import Lemma.Algebra.Eq_DivProd_ProdTail.of.GtLength_0.Gt_0
import Lemma.Algebra.Eq_Mul_ProdTail_Prod.of.GtLength_0.Gt_0
import Lemma.Algebra.EqHeadD.of.GtLength_0
import Lemma.Algebra.EqHeadD.of.EqLength_0
import Lemma.Algebra.Length.le.One.of.Tail.eq.Nil
import Lemma.Algebra.TailTail.eq.Drop_2
import Lemma.Algebra.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
import Lemma.Algebra.EqMin_SubMulS
open Algebra

/--
the concept of a Tensor is a generalization of a matrix, like the Tensor concept in pytorch / tensorflow
the declaration syntax is similar
```lean
-- in lean:
import sympy.tensor.tensor
def n : ℕ := 2
def m : ℕ := 2
def l : ℕ := 2
def t : Tensor Float [n, m, l] := ⟨List.replicate (n * m * l) default, rfl⟩
#print t
```
```python
# in pytorch:
from torch import Tensor
n : int = 2
m : int = 2
l : int = 2
t = torch.Tensor(m, n, l).to(dtype=torch.float)
print(t)
```
-/
structure Tensor (α : Type _) (shape : List ℕ) where
  data : List.Vector α shape.prod


def Tensor.length  (t : Tensor α shape)  : ℕ :=
  match shape with
  | [] => 0
  | length :: _ => length


def Tensor.shape (_ : Tensor α s)  : List ℕ :=
  s


instance [Inhabited α] : Inhabited (Tensor α shape) where
  default := ⟨List.replicate shape.prod default, by simp⟩


def Tensor.toVector (t : Tensor α s) : List.Vector (Tensor α s.tail) (s.headD 0) :=
  if h_GtLength_0 : s.length > 0 then
    have h_EqHeadD := EqHeadD.of.GtLength_0 h_GtLength_0 0
    if h_GtGetElem_0 : s[0] > 0 then
      let rows := s[0] -- the number of rows
      let cols := t.data.length / rows -- the number of columns
      have h_precondition : s.prod = t.data.length := by simp
      have h_eq_prod_tail := Eq_DivProd_ProdTail.of.GtLength_0.Gt_0 h_GtLength_0 h_GtGetElem_0
      have h_eq_prod_tail : s.tail.prod = t.data.length / rows := h_precondition ▸ h_eq_prod_tail
      have h_eq_prod_tail : s.tail.prod = cols := by rw [h_eq_prod_tail]
      have h_eq_mul := Eq_Mul_ProdTail_Prod.of.GtLength_0.Gt_0 h_GtLength_0 h_GtGetElem_0
      have h_eq_mul : t.data.length = rows * cols := by
        rw [h_precondition, h_eq_prod_tail] at h_eq_mul
        exact h_eq_mul
      let v : List.Vector (Tensor α s.tail) rows := (List.Vector.range rows).map fun i : Fin rows =>
        -- iterate over the slices
        have h_Eq : (cols ⊓ (s.prod - ↑i * cols)) = s.tail.prod := by
          rw [(show s.prod = t.data.length by simp)]
          rw [h_eq_mul]
          rw [h_eq_prod_tail]
          apply EqMin_SubMulS
        ⟨cast (by rw [h_Eq]) (t.data.substr (i * cols) cols)⟩
      cast (by rw [(show rows = s.headD 0 by rw [h_EqHeadD])]) v
    else
      ⟨
        [],
        by
          rw [h_EqHeadD]
          simp
          rw [(show s[0] = 0 by linarith)]
      ⟩
  else
    ⟨
      [],
      by
        rw [EqHeadD.of.EqLength_0 (show s.length = 0 by linarith)]
        simp
    ⟩


def Zeros [Zero α] (shape : List ℕ) : Tensor α shape :=
  ⟨List.replicate shape.prod 0, by simp⟩


def Ones [One α] (shape : List ℕ) : Tensor α shape :=
  ⟨List.replicate shape.prod 1, by simp⟩


instance [Mul α] : Mul (Tensor α s) where
  mul a b := ⟨a.data.val.zipWith HMul.hMul b.data.val , by simp [Tensor.data]⟩


def Tensor.get [Inhabited α] (t : Tensor α s) (i : ℤ) : Tensor α s.tail :=
  let i := Slice.Add_Mul_DivSub1Sign_2 t.length i
  if h_i : i < 0 ∨ i ≥ t.length then
    default
  else
    have h_i : i ≥ 0 ∧ i < t.length := by
      simp at h_i
      assumption
    have h_Eq_i : i = i.toNat := by
      simp
      exact h_i.1
    let i : Nat := i.toNat
    have h_i : i < t.length := by
      rw [h_Eq_i] at h_i
      norm_cast at h_i
      simp [i]
      exact h_i.2
    let i : Fin t.length := ⟨i, h_i⟩
    have h_GtLength_0 : s.length > 0 := by
      match s with
      | [] =>
        contradiction
      | length :: _ =>
        simp
    have h_EqHeadD := EqHeadD.of.GtLength_0 h_GtLength_0 0
    have h_Eq : s[0] = t.length := by
      match s with
      | [] =>
        contradiction
      | lenght :: _ =>
        simp [Tensor.length]
    have := h_EqHeadD.trans h_Eq
    t.toVector[i]

instance [Inhabited α] : GetElem (Tensor α [n]) ℤ α fun _ _ => True where
  getElem v i _ := (v.get i).data[0]

instance [Inhabited α] : GetElem (Tensor α [n]) ℕ α fun _ _ => True where
  getElem v i _ := v[(i : ℤ)]

instance [Inhabited α] : GetElem (Tensor α shape) ℤ (Tensor α shape.tail) fun _ _ => True where
  getElem v i _ := v.get i

instance [Inhabited α] : GetElem (Tensor α shape) ℕ (Tensor α shape.tail) fun _ _ => True where
  getElem v i _ := v[(i : ℤ)]


/--
Represents a mathematical object with indices.
X[i, j, k].shape = X.shape.drop 3
-/
def Indexed [Inhabited α] (base : Tensor α shape) (indices : List ℤ) : Tensor α (shape.drop indices.length) :=
  match indices with
  | .nil =>
    base
  | index :: indices =>
    have h_Eq : shape.drop (index :: indices).length = shape.tail.drop indices.length := by simp
    cast (by rw [h_Eq]) (Indexed base[index] indices)

def Tensor.getSlice
  [Inhabited α]
  (t : Tensor α s)
  (slice : Slice) :
  Tensor α (slice.length t.length :: s.tail) :=
  let tensors := (List.Vector.indices slice t.length).map fun i =>
    t[i].data
  ⟨tensors.flatten.val, by simp⟩

def Tensor.getSlice2
  [Inhabited α]
  (t : Tensor α s)
  (slice0 : Slice)
  (slice1 : Slice)
  {h_shape : s.length ≥ 2} :
  Tensor α (slice0.length s[0] :: slice1.length s[1] :: s.drop 2) :=
  let tensors := (List.Vector.indices slice0 s[0]).map fun i : Fin s[0] =>
    have h_Eq : t[(i : ℕ)].length = s[1] := by
      unfold Tensor.length
      match h_s : s.tail, t[i] with
      | [], _ =>
        simp
        have := Length.le.One.of.Tail.eq.Nil h_s
        linarith
      | s1 :: rest, _ =>
        simp
        have h_Eq : (s1::rest)[0] = s1 := by
          simp
        simp [← h_s] at h_Eq
        exact h_Eq.symm
    let data : List.Vector α (slice1.length s[1] * (s.drop 2).prod) := ⟨
      (t[i].getSlice slice1).data.val,
      by
        simp
        rw [h_Eq, TailTail.eq.Drop_2]
    ⟩
    data
  ⟨tensors.flatten.val, by simp⟩


def Tensor.getSlice3 [Inhabited α] (t : Tensor α s) (slice0 : Slice) (slice1 : Slice) (slice2 : Slice) {h_shape : s.length ≥ 3} : Tensor α (slice0.length s[0] :: slice1.length s[1] :: slice2.length s[2] :: s.drop 3) :=
  let indices : List.Vector (Fin s[0]) (slice0.length s[0]) := List.Vector.indices slice0 s[0]
  let tensors : List.Vector (List.Vector α (slice1.length s[1] * (slice2.length s[2] * (List.drop 3 s).prod))) (slice0.length s[0]) := indices.map fun i : Fin s[0] =>
    have h_Eq : t[(i : ℕ)].length = s[1] := by
      unfold Tensor.length
      match h_s : s.tail, t[i] with
      | [], _ =>
        simp
        have := Length.le.One.of.Tail.eq.Nil h_s
        linarith
      | s1 :: rest, _ =>
        simp
        have h_Eq : (s1::rest)[0] = s1 := by
          simp
        simp [← h_s] at h_Eq
        exact h_Eq.symm
    let ti : Tensor α (s.drop 1) := ⟨t[i].data.val, by simp⟩
    have h_shape : (s.drop 1).length ≥ 2 := LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1 (by norm_num) h_shape
    ⟨(ti.getSlice2 (h_shape := h_shape) slice1 slice2).data.val, by simp⟩
  ⟨tensors.flatten.val, by simp⟩


def Sliced
  [Inhabited α]
  (t : Tensor α s)
  (slices : List Slice)
  {h_shape : s.length ≥ slices.length} :
  Tensor α ((slices.enumerate.map fun ⟨i, slice⟩ => slice.length s[i]) ++ s.drop slices.length) :=
  let shape := (slices.enumerate.map fun ⟨i, slice⟩ => slice.length s[i])
  match h_slice : slices with
  | [] =>
    t
  | slice :: slices' =>
    have : s.length > 0 := by
      simp at h_shape
      linarith
    let indices : List.Vector (Fin s[0]) (slice.length s[0]) := List.Vector.indices slice s[0]
    let tensors : List.Vector (List.Vector α ((shape.drop 1).prod * (List.drop slices'.length s).prod)) (slice.length s[0]) := indices.map fun i : Fin s[0] =>
      sorry
    sorry

-- def SlicedIndexed (a : Tensor α s) (indices : List ℕ) :  Tensor α s :=
--   sorry

-- instance [Inhabited α] : Dot (Tensor α (batch_size ++ [l, m])) (Tensor α (batch_size ++ [m, n])) (Tensor α (batch_size ++ [l, n])) := ⟨Tensor.dot⟩
-- def Tensor.getitem [Inhabited α] (t : Tensor α s) (i : ℕ) : α :=
-- (M @ N)[..., i, j] = (M[..., i, :] * N[..., j]).sum(-1)
-- #check Matrix.mul_apply
-- def Tensor.dot [Inhabited α] (M : Tensor α (batch_size ++ [l, m])) (N : Tensor α (batch_size ++ [m, n])) : Tensor α (batch_size ++ [l, n]) :=
-- fun i k => (fun j => M i j) ⬝ᵥ fun j => N j k
