import sympy.vector.vector
import Lemma.Bool.EqUFnS.of.Eq
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Nat.Lt.of.Mk.eq.IteGt.Ne
import Lemma.Nat.EqMaxS.of.Mk.eq.IteGt
import Lemma.Nat.EqMulDiv.of.Dvd
import Lemma.Int.NegSucc.eq.NegAdd_1
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.List.ProdSet__MulGet.eq.Mul_Prod
import Lemma.List.EraseIdx_Succ.eq.Cons_EraseIdxTail.of.Lt_LengthTail
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx.of.Le_Length
import Lemma.List.SwapAppend.eq.Append_Swap.of.Ge_Length.Ge_Length
import Lemma.List.EqSwap_0'1
import Lemma.List.ProdSwap.eq.Prod
import Lemma.List.Rotate_Mod.eq.Rotate
import Lemma.List.EqPermute__0
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.Take.eq.Nil.of.Eq_0
import Lemma.List.EqDrop.of.Eq_0
import Lemma.List.LengthDrop.eq.SubLength
import Lemma.List.Swap.eq.PermutePermute.of.Lt.Lt_Length
import Lemma.List.EqSwapS.of.Mk.eq.IteGt
import Lemma.List.EqEraseIdx.of.Ge_Length
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.List.ProdPermute.eq.MulProd_ProdAppend
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.List.ProdPermute__Neg.eq.MulProd_ProdDrop.of.Val.ne.SubLength_1
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.List.Rotate.eq.AppendDrop__Take
open Bool Nat Int List

/--
the concept of a Tensor is a generalization of a matrix, like the Tensor concept in pytorch / tensorflow
the declaration syntax is similar
```lean
-- in lean:
import sympy.tensor.tensor
def n : ℕ := 2
def m : ℕ := 2
def l : ℕ := 2
def X : Tensor Float [n, m, l] := ⟨List.Vector.replicate (n * m * l) default⟩
#print X
```
```python
# in pytorch:
from torch import Tensor
n : int = 2
m : int = 2
l : int = 2
X = torch.Tensor(m, n, l).to(dtype=torch.float)
print(X)
```
-/
structure Tensor (α : Type _) (shape : List ℕ) where
  data : List.Vector α shape.prod

def Tensor.length  (X : Tensor α shape)  : ℕ :=
  match shape with
  | [] => 0
  | length :: _ => length

def Tensor.shape (_ : Tensor α s)  : List ℕ := s

instance [Inhabited α] : Inhabited (Tensor α shape) where
  default := ⟨default⟩

def Tensor.toVector (X : Tensor α s) : List.Vector (Tensor α s.tail) (s.headD 1) :=
  cast (by rw [ProdTake_1.eq.HeadD_1]) ((X.data.splitAt 1).map fun v : List.Vector α (s.drop 1).prod => (⟨cast (by simp) v⟩ : Tensor α s.tail))

instance [Zero α] : Zero (Tensor α s) := ⟨⟨Zero.zero⟩⟩

instance [One α] : One (Tensor α s) := ⟨⟨One.one⟩⟩

instance [AddMonoidWithOne α] [CharZero α] : NatCast (Tensor α []) where
  natCast n := ⟨[n], by simp⟩

instance : Coe α (Tensor α []) where
  coe x := ⟨[x], by simp⟩

instance [Add α] : Add (Tensor α s) where
  add A B := ⟨A.data + B.data⟩

/--
broadcast addition of tensors
instance [Add α] : HAdd (Tensor α s) α (Tensor α s) where
  hAdd A B := A + (B : Tensor α [])
-/
instance [Add α] : HAdd (Tensor α s) (Tensor α []) (Tensor α s) where
  hAdd A B :=
    let B : Tensor α s := ⟨List.Vector.replicate s.prod B.data[0]⟩
    A + B

instance [Add α] : HAdd (Tensor α (n :: s).tail) (Tensor α s) (Tensor α s) where
  hAdd A B :=
    let A : Tensor α s := A
    A + B

instance [Mul α] : Mul (Tensor α s) where
  mul A B := ⟨A.data * B.data⟩

instance [Mul α] : HMul (Tensor α s) α (Tensor α s) where
  hMul A b := ⟨A.data * b⟩

instance [Div α] : Div (Tensor α s) where
  div A B := ⟨A.data / B.data⟩

instance [Div α] : HDiv (Tensor α s) α (Tensor α s) where
  hDiv A b := ⟨A.data / b⟩

instance [Div α] : HDiv (Tensor α s) (Tensor α []) (Tensor α s) where
  hDiv A b := ⟨A.data / b.data[0]⟩

instance [Neg α] : Neg (Tensor α s) where
  neg X := ⟨-X.data⟩

instance [Inv α] : Inv (Tensor α s) where
  inv X := ⟨X.data⁻¹⟩

instance [Mul α] : HMul (Tensor α [m, n].tail.tail) (Tensor α [m', n'].tail.tail) (Tensor α []) where
  hMul A B :=
    let A : Tensor α [] := A
    let B : Tensor α [] := B
    A * B

instance [Mul α] : HMul (Tensor α []) (Tensor α [m, n].tail.tail) (Tensor α []) where
  hMul A B :=
    let B : Tensor α [] := B
    A * B

instance [Mul α] : HMul (Tensor α [m, n].tail.tail) (Tensor α []) (Tensor α []) where
  hMul A B :=
    let A : Tensor α [] := A
    A * B

instance [Mul α] : HMul (Tensor α (n :: s).tail) (Tensor α s) (Tensor α s) where
  hMul A B :=
    let A : Tensor α s := A
    A * B

instance [Mul α] : HMul (Tensor α s) (Tensor α []) (Tensor α s) where
  hMul A b := ⟨A.data * b.data[0]⟩

/-- Append two vectors. -/
def Tensor.append (xs : Tensor α (n :: s)) (ys : Tensor α (m :: s)) : Tensor α ((n + m) :: s) :=
  ⟨cast (by simp; rw [right_distrib]) (xs.data ++ ys.data)⟩

instance : HAppend (Tensor α (n :: s)) (Tensor α (m :: s)) (Tensor α ((n + m) :: s)) where
  hAppend := Tensor.append

def Tensor.fromVector (X : List.Vector (Tensor α s) n) : Tensor α (n :: s) :=
  ⟨(X.map Tensor.data).flatten⟩

/--
[torch.sum](https://docs.pytorch.org/docs/stable/generated/torch.sum.html)
use (X.sum dim).keepdim to keep the dimension
-/
def Tensor.sum [Add α] [Zero α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  if h_dim : dim < s.length then
    match h : dim with
    | .zero =>
      ⟨cast (by simp) (X.data.splitAt 1).sum⟩
    | .succ dim =>
      have h_lt : dim < s.tail.length := by
        simp
        simp at h_dim
        apply Lt_Sub.of.LtAdd h_dim
      cast
        (by simp_all [EraseIdx_Succ.eq.Cons_EraseIdxTail.of.Lt_LengthTail h_lt 1])
        (Tensor.fromVector (X.toVector.map (·.sum dim)))
  else
    cast (by
      simp at h_dim
      rw [EqEraseIdx.of.Ge_Length h_dim]
    ) X

/--
[torch.mean](https://pytorch.org/docs/stable/generated/torch.mean.html)

Compute the mean of a tensor along a given dimension.
-/
def Tensor.mean [Add α] [Zero α] [Div α] [NatCast α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  let size := if h_dim : dim < s.length then s.get ⟨dim, h_dim⟩ else 1
  X.sum dim / (size : α)

/--
index the tensor physically, i.e. calculate the (row-major (C-style)) index in the data vector
given:
  - `indices` - the indices of the tensor
  - `shape` - the shape of the tensor
assuming that indices and shape have the same length
-/
def Tensor.physicalIndex (indices : List ℕ) (shape : List ℕ) : ℕ :=
  let pairs := List.zip indices shape
  let (res, _) := List.foldr
    (fun (i, d) (acc, mult) => (acc + i * mult, mult * d))
    (0, 1)
    pairs
  res

/--
calculate the logical indices of a tensor given the physical index
given:
  - `index` - the physical index of the tensor
  - `shape` - the shape of the tensor
-/
def Tensor.logicalIndices (index : ℕ) (shape : List ℕ) : List ℕ :=
  if shape.any (· == 0) then
    List.replicate shape.length 0
  else
    let rec computeIdx : ℕ → List ℕ → List ℕ → List ℕ
      | _, [], _ => []
      | rem, _ :: ds, acc =>
        let prod := ds.prod
        let idx := rem / prod
        let rem' := rem % prod
        idx :: computeIdx rem' ds acc
    computeIdx index shape []

/--
[torch.unsqueeze](https://docs.pytorch.org/docs/stable/generated/torch.unsqueeze.html)

given :

X : Tensor α [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉]

t' = X.unsqueeze 4

t': Tensor α [s₀, s₁, s₂, s₃, 1, s₄, s₅, s₆, s₇, s₈, s₉]

the following eqaulity holds:

X[i₀, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, i₉] = t'[i₀, i₁, i₂, i₃, 0, i₄, i₅, i₆, i₇, i₈, i₉]
-/
def Tensor.unsqueeze (X : Tensor α s) (dim : ℕ) : Tensor α (s.insertIdx dim 1) :=
  let s' := s.insertIdx dim 1
  have h_prod := ProdInsertIdx.eq.Prod s dim
  let data : List.Vector α s'.prod := (List.Vector.range s'.prod).map fun i =>
    let i : Fin s.prod := cast (by rw [h_prod]) i
    X.data[i]
  ⟨data⟩

/--
[torch.repeat_interleave](https://docs.pytorch.org/docs/stable/generated/torch.repeat_interleave.html)
[numpy.repeat](https://numpy.org/doc/stable/reference/generated/numpy.repeat.html)

given :

X : Tensor α [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉]

t' = X.repeat 3 4

t': Tensor α [s₀, s₁, s₂, s₃, s₄ * 3, s₅, s₆, s₇, s₈, s₉]

the following eqaulity holds:
∀ X : Fin 3,
  X[i₀, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, i₉] = t'[i₀, i₁, i₂, i₃, i₄ + s₄ * X, i₅, i₆, i₇, i₈, i₉]
-/
def Tensor.repeat (X : Tensor α s) (k : ℕ) (dim : Fin s.length) : Tensor α (s.set dim (k * s[dim])) :=
  ⟨cast
    (by
      congr
      rw [ProdSet__MulGet.eq.Mul_Prod dim k]
      rw [Mul_Mul.eq.MulMul]
      rw [mul_comm (b := k)]
      rw [MulMul.eq.Mul_Mul]
      apply EqMulS.of.Eq.left
      simp
    )
    ((X.data.splitAt dim).map (·.repeat k)).flatten
  ⟩

def Tensor.rotate (X : Tensor α s) (i : ℕ): Tensor α (s.rotate i) :=
  let k := i % s.length
  let data : List.Vector α (List.drop k s ++ List.take k s).prod := cast (by simp) (X.data.splitAt k).transpose.flatten
  ⟨cast (by rw [AppendDrop__Take.eq.Rotate s i]) data⟩

def Tensor.permuteHead (X : Tensor α s) (size : ℕ) : Tensor α ((s.take size).rotate 1 ++ s.drop size) :=
  let X : Tensor _ (s.take size) := ⟨X.data.splitAt size⟩
  let X := X.rotate 1
  ⟨cast (by simp_all) X.data.flatten⟩

def Tensor.permuteTail (X : Tensor α s) (size : ℕ) : Tensor α (s.take (s.length - size) ++ (s.drop (s.length - size)).rotate (size ⊓ s.length - 1)) :=
  let data : List.Vector (List.Vector α ((s.drop (s.length - size)).rotate (size ⊓ s.length - 1)).prod) (s.take (s.length - size)).prod := (X.data.splitAt (s.length - size)).map fun data =>
    let X : Tensor _ (s.drop (s.length - size)) := ⟨data⟩
    (X.rotate (size ⊓ s.length - 1)).data
  ⟨cast (by simp_all) data.flatten⟩

/--
[torch.permute](https://docs.pytorch.org/docs/stable/generated/torch.permute.html)
-/
def Tensor.permute (X : Tensor α s) (i : Fin s.length) (d : ℤ) : Tensor α (s.permute i d) :=
  match d with
  | .ofNat d =>
    match d with
    | .zero =>
      cast (by simp [EqPermute__0]) X
    | .succ d =>
      if h : i.val = 0 then
        have := Permute.eq.AppendRotateTake___Drop.of.EqVal_0 h d.succ
        cast (by simp_all) (X.permuteHead (d + 2))
      else
        have := ProdPermute.eq.MulProd_ProdAppend i d.succ
        ⟨cast (by simp_all) ((X.data.splitAt i).map fun data => ((⟨data⟩ : Tensor α (s.drop i)).permuteHead (d + 2)).data).flatten⟩
  | .negSucc d =>
    if h : i.val = s.length - 1 then
      have := Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h d.succ
      cast (by simp_all [NegSucc.eq.NegAdd_1]) (X.permuteTail (d + 2))
    else
      have := ProdPermute__Neg.eq.MulProd_ProdDrop.of.Val.ne.SubLength_1 h d.succ
      ⟨cast (by simp_all [NegSucc.eq.NegCoeAdd_1]) ((⟨X.data.splitAt (i + 1)⟩ : Tensor (List.Vector α (s.drop (i + 1)).prod) (s.take (i + 1))).permuteTail (d + 2)).data.flatten⟩

/--
[torch.transpose](https://docs.pytorch.org/docs/stable/generated/torch.transpose.html)
-/
def Tensor.transpose (X : Tensor α s) (i : ℕ) (j : ℕ): Tensor α (s.swap i j) :=
  if h_eq : i = j then
    cast (by simp_all [EqSwap]) X
  else if h : i ≥ s.length ∨ j ≥ s.length then
    cast
      (by
        obtain hi | hj := h
        .
          simp_all [EqSwap.of.Ge_Length.left]
        .
          simp_all [EqSwap.of.Ge_Length]
      )
      X
  else
    have h : i ⊔ j < s.length := by
      simp_all
    let args : ℕ × ℕ := if i > j then ⟨j, i⟩ else ⟨i, j⟩
    have h_ite : (args : ℕ × ℕ) = if i > j then ⟨j, i⟩ else ⟨i, j⟩ := rfl
    let ⟨i, j⟩ := args
    have h_lt := Lt.of.Mk.eq.IteGt.Ne h_eq h_ite
    have h : i ⊔ j < s.length := by
      simp_all [EqMaxS.of.Mk.eq.IteGt h_ite]
    have h_i : i < s.length := by
      simp_all
    have h_j : j < s.length := by
      simp_all
    let d := j - i
    have h_j' : j < (s.permute ⟨i, h_i⟩ (d - 1)).length := by
      simpa
    cast
      (by
        apply EqUFnS.of.Eq (f := Tensor α)
        rw [PermutePermute.eq.Swap.of.Lt.Lt_Length h_j h_lt]
        rw [EqSwapS.of.Mk.eq.IteGt h_ite]
      )
      ((X.permute ⟨i, h_i⟩ (d - 1)).permute ⟨j, h_j'⟩ (-d))

def Tensor.T (X : Tensor α s) : Tensor α (s.swap (s.length - 2) (s.length - 1)) :=
  X.transpose (s.length - 2) (s.length - 1)

postfix:1024 "ᵀ" => Tensor.T

def Tensor.dot [Mul α] [Add α] [Zero α] (A : Tensor α (batch_size ++ [m, k])) (B : Tensor α (batch_size ++ [k, n])) : Tensor α (batch_size ++ [m, n]) :=
  let A : Tensor α (batch_size ++ [m, 1, k]) := cast
    (by simp_all [InsertIdxAppend.eq.Append_InsertIdx])
    (A.unsqueeze (batch_size.length + 1))
  let A : Tensor α (batch_size ++ [m, n, k]) := cast
    (by simp)
    (A.repeat n ⟨batch_size.length + 1, by simp⟩)
  let B : Tensor α (batch_size ++ [n, k]) := cast
    (by
      rw [SwapAppend.eq.Append_Swap.of.Ge_Length.Ge_Length (by simp) (by simp)]
      simp [EqSwap_0'1]
    )
    B.T
  let B : Tensor α (batch_size ++ [1, n, k]) := cast
    (by
      rw [InsertIdxAppend.eq.Append_InsertIdx.of.Le_Length (by simp)]
      simp
    )
    (B.unsqueeze batch_size.length)
  let B : Tensor α (batch_size ++ [m, n, k]) := cast
    (by simp)
    (B.repeat m ⟨batch_size.length, by simp⟩)
  let C : Tensor α (batch_size ++ [m, n]) := cast
    (by simp_all [EraseIdxAppend.eq.Append_EraseIdx])
    ((A * B).sum (batch_size.length + 2))
  C

class MatMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /--
  python's matmul operator
  -/
  dot : α → β → γ

@[inherit_doc] infixl:70 " @ " => MatMul.dot

instance [Mul α] [Add α] [Zero α] : MatMul (Tensor α (batch_size ++ [m, k])) (Tensor α (batch_size ++ [k, n])) (Tensor α (batch_size ++ [m, n])) := ⟨Tensor.dot⟩

instance [Mul α] [Add α] [Zero α] : MatMul (Tensor α [m, k]) (Tensor α [k, n]) (Tensor α [m, n]) where
  dot A B :=
    let A : Tensor α ([] ++ [m, k]) := A
    A.dot B

def Tensor.map (f : α → β) (X : Tensor α s) : Tensor β s :=
  ⟨X.data.map f⟩

instance [Coe α β] : Coe (Tensor α s) (Tensor β s) where
  coe X := X.map (fun a => Coe.coe a)

instance : Coe Bool ℕ where
  coe b := b.toNat

instance [NatCast α] : Coe ℕ α where
  coe n := (n : α)

def Tensor.broadcast (X : Tensor α s) (S : List ℕ) (h : s.prod ∣ S.prod) : Tensor α S :=
  ⟨cast (by rw [EqMulDiv.of.Dvd h]) (X.data.repeat (S.prod / s.prod))⟩
