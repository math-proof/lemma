import Lemma.Algebra.LengthToList.eq.Length
import Lemma.Algebra.EqMin_SubMulS
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
open Algebra


class Dot (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  dot : α → β → γ

infix:70 " ⬝ " => Dot.dot

namespace List.Vector

/--
Implement the instance for Vector
-/
instance : IsConstant (Vector α n) where
  is_constant v := v.val is constant

def dot [Add α] [Zero α] [Mul α] (v1 v2 : Vector α n) : α :=
  match n, v1, v2 with
  | 0, ⟨[], _⟩, ⟨[], _⟩ => 0
  | n + 1, ⟨x :: xs, h₁⟩, ⟨y :: ys, h₂⟩ =>
    have h₁ : xs.length = n := by
      simp [List.length] at h₁
      assumption
    have h₂ : ys.length = n := by
      simp [List.length] at h₂
      assumption
    x * y + dot ⟨xs, h₁⟩ ⟨ys, h₂⟩


instance [Add α] [Zero α] [Mul α] : Dot (Vector α n) (Vector α n) α := ⟨dot⟩

def sum [Add α] [Zero α] : Vector α n → α
  | ⟨v, _⟩ => v.sum

def headD : Vector α n → α → α
  | ⟨v, _⟩, d => v.headD d

def push {n : ℕ} (v : Vector α n) (x : α) : Vector α (n + 1) :=
  match n with
  | 0 => x ::ᵥ .nil
  | _ + 1 => v.head ::ᵥ (push v.tail x)

def range (n : Nat) : Vector (Fin n) n :=
  ⟨
    List.range n |>.pmap
      (
        fun i hi =>
          ⟨i, (List.mem_range (n := n) (m := i)).mp hi⟩
      )
      (by simp),
    by simp
  ⟩

def indices (s : Slice) (n : ℕ) : Vector (Fin n) (s.length n) :=
  ⟨s.toList n, LengthToList.eq.Length (s := s) (n := n)⟩

def flatten (xs : Vector (Vector α n) m) : Vector α (m * n) :=
  ⟨(xs.toList.map Vector.toList).flatten, by rcases xs; simp_all [Function.comp_def, List.map_const']⟩

def array_slice (L : Vector α n) (start : Nat) (step : Nat) : Vector α (min step (n - start)) :=
  (take (step) ∘ drop start) L

def unflatten (xs : Vector α (m * n)) : Vector (Vector α n) m :=
  (range m).map fun i : Fin m => cast (by rw [EqMin_SubMulS]) (xs.array_slice (i * n) n)

/--
```python
a = [*range(10)]
```
def a : List ℕ := List.range 10
def a : List.Vector (Fin 10) 10 := List.Vector.range 10
#eval a
#eval a[-1:-1:-1]   -- []
#eval a[-1:-10:-1]  -- [9, 8, 7, 6, 5, 4, 3, 2, 1]
#eval a[9:0:-1]     -- [9, 8, 7, 6, 5, 4, 3, 2, 1]
#eval a[-10:-11:-1] -- [0]
#eval a[0:-1:-1]    -- []
#eval a[-20:-9]     -- [0]
#eval a[1:-2:5]     -- [1, 6]
#eval a[0:9:2]      -- [0, 2, 4, 6, 8]
#eval a[-2:0:-2]    -- [8, 6, 4, 2]
#eval a[-2:]    -- [8, 9]
-/
def getSlice (L : Vector α n) (s : Slice) : Vector α (s.length n) :=
  (indices s L.length).map fun i => L[i]

instance [Add α] : Add (Vector α n) where
  add a b := a.map₂ HAdd.hAdd b

instance [Mul α] : Mul (Vector α n) where
  mul a b := a.map₂ HMul.hMul b

instance [Mul α] : HMul (Vector α n) α (Vector α n) where
  hMul a b := a.map (· * b)

instance [Div α] : Div (Vector α n) where
  div a b := a.map₂ HDiv.hDiv b

instance [Div α] : HDiv (Vector α n) α (Vector α n) where
  hDiv a b := a.map (· / b)

instance [Zero α] : Zero (Vector α n) where
  zero := Vector.replicate n 0

instance [One α] : One (Vector α n) where
  one := Vector.replicate n 1

instance [Inv α] : Inv (Vector α n) where
  inv a := a.map (·⁻¹)

def transpose (xs : Vector (Vector α n) m) : Vector (Vector α m) n :=
  (range n).map fun j => (range m).map fun i => xs[i][j]

def splitAt {s : List ℕ} (v : Vector α s.prod) (d : ℕ) : Vector (Vector α (s.drop d).prod) (s.take d).prod :=
  let v : Vector α ((s.take d).prod * (s.drop d).prod) := cast (by rw [Prod.eq.MulProdTake__ProdDrop]) v
  v.unflatten

end List.Vector

def List.Vector.repeat (x : Vector α n) (m : ℕ) : Vector α (m * n) :=
  (List.Vector.replicate m x).flatten
