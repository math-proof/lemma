import Instance.Data.Vector.Vector
import Instance.Analysis.SpecialFunctions.Exponential.Part5
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Theorem.Analysis.Real.Relational
import Instance.Data.Vector.Functions
open Vector


namespace List.Vector

def softmax [Exp α] (x : Vector α n) : Vector α n :=
  let x_exp := Exp.exp x
  x_exp / x_exp.sum

def sigmoid [Exp α] (x : Vector α n) : Vector α n :=
  1 / (1 + Exp.exp (-x))

def argminmax [NeZero n] (x : Vector α n) (cmp : α → α → Prop) [DecidableRel cmp] : Fin n :=
  Nat.rec
    (motive := fun n => (n ≠ 0) → Vector α n → Fin n)
    (fun h_n _ => False.elim (h_n rfl))
    (fun n ih _ v =>
      if h_n : n = 0 then
        0
      else
        let i := ih h_n v.tail
        if cmp v.head (v.tail.get i) then
          i.succ
        else
          0
    )
    n (NeZero.ne n) x

def argmin [NeZero n] [LT α] [DecidableLT α] (x : Vector α n) : Fin n := x.argminmax GT.gt

def argmax [NeZero n] [LT α] [DecidableLT α] (x : Vector α n) : Fin n := x.argminmax LT.lt

/--
def v : List.Vector Float 5 := ⟨[3, 1, 4, 1, 5], by simp⟩
#eval v.min  -- Output: 1
-/
def min [NeZero n] [LT α] [DecidableLT α] (x : Vector α n) : α := x.get x.argmin

/--
```lean
def v : List.Vector Float 4 := ⟨[2.5, 3.6, 1.2, 4.8], by simp⟩
#eval v.max  -- Output: 4.8
```
-/
def max [NeZero n] [LT α] [DecidableLT α] (x : Vector α n) : α := x.get x.argmax

/--
array minimum / maximum of each row column in a matrix, similar to `Tensor.aminmax` in PyTorch
-/
def aminmax [NeZero m] (x : Vector (Vector α n) m) (cmp : α → α → Prop) [DecidableRel cmp] : Vector α n :=
  x.transpose.map (fun v => v.get (v.argminmax cmp))

/--
Returns the array index of the minimum/maximum element for each column.
-/
def argAminmax [NeZero m] (x : Vector (Vector α n) m) (cmp : α → α → Prop) [DecidableRel cmp] : Vector (Fin m) n :=
  x.transpose.map (fun v => v.argminmax cmp)

end List.Vector
