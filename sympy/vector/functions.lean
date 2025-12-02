import sympy.vector.vector
import sympy.functions.elementary.exponential
open Vector

namespace List.Vector

instance [Exp α] : Exp (Vector α n) where
  exp a := a.map Exp.exp
  exp_add x y := by
    ext i
    simp [GetMul.eq.MulGetS.fin]
    rw [GetAdd.eq.AddGetS.fin]
    apply Exp.exp_add
  exp_zero := by
    ext i
    simp [Zero.eq.Replicate]
    simp [One.eq.Replicate]
    apply Exp.exp_zero
  exp_neg x := by
    ext i
    simp [GetInv.eq.InvGet.fin]
    simp [GetNeg.eq.NegGet.fin]
    apply Exp.exp_neg

instance [NeZero n] [ExpNeZero α] : ExpNeZero (Vector α n) where
  exp_ne_zero x := by
    simp [Exp.exp]
    intro h_eq
    have h_head := EqGetS.of.Eq.fin h_eq ⟨0, NeZero.pos n⟩
    simp at h_head
    simp [Zero.eq.Replicate] at h_head
    simp [ExpNeZero.exp_ne_zero] at h_head


instance [Log α] : Log (Vector α n) where
  log a := a.map Log.log


def softmax [Div α] [Exp α] (x : Vector α n) : Vector α n :=
  let x_exp := exp x
  x_exp / x_exp.sum

private def argminmax [NeZero n] (x : Vector α n) (cmp : α → α → Prop) [DecidableRel cmp] : Fin n :=
  Nat.rec
    (motive := fun n => n ≠ 0 → Vector α n → Fin n)
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
