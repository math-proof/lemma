import Lemma.Algebra.LtSub_1.of.Le.Gt_0
open Algebra


/--
if index is nonnegative, it refers to the i-th element of the list
if index is negative, it refers to the (length + i)-th element of the list
-/
structure Slice where
  start : ℤ
  stop : ℤ
  step : ℤ := 1

def Slice.Add_Mul_DivSub1Sign_2 (n : ℕ) (i : ℤ) : ℤ := i + n * ((1 - Int.sign i) / 2)

def Nat.sliced_indices (h_start : start < stop) (h_stop : stop ≤ n) (h_step : step > 0) : List (Fin n) :=
  -- now we have start < stop ≤ n and step > 0
  ⟨start, lt_of_lt_of_le h_start h_stop⟩ :: (if h_start : start + step < stop then Nat.sliced_indices h_start h_stop h_step else [])


/--
search valid indices within closed interval [stop, start]
start is the first index
start - step is the next index, etc
-/
def Nat.sliced_indices' (h_stop : start > stop) (h_start : start ≤ n) (h_step : step > 0) : List (Fin n) :=
  -- now we have stop < start ≤ n and step > 0
  ⟨start - 1, LtSub_1.of.Le.Gt_0 (by linarith [Gt.of.Ge.Gt h_start h_stop]) h_start⟩ :: (if h_stop : start - step > stop then Nat.sliced_indices' h_stop (show start - step ≤ n by simp; linarith) h_step else [])


def Slice.toList (s : Slice) (n : ℕ) : List (Fin n) :=
  match s.step with
  | .ofNat step =>
    match step with
    | .zero =>
      []
    | .succ step =>
      -- step is positive
      let start := (Add_Mul_DivSub1Sign_2 n s.start).toNat
      let stop := (Add_Mul_DivSub1Sign_2 n s.stop).toNat.min n
      if h_Ge : start ≥ stop then
        []
      else
        have h_start : start < stop := by
          simp at h_Ge
          assumption
        have h_stop : stop ≤ n := by
          simp [stop]
        Nat.sliced_indices h_start h_stop (Nat.succ_pos step)
  | .negSucc step =>
    -- step is negative
    let start := (Add_Mul_DivSub1Sign_2 n s.start + 1).toNat.min n
    let stop := (Add_Mul_DivSub1Sign_2 n s.stop + 1).toNat
    if h_Le : start ≤ stop then
      []
    else
      have h_start : start ≤ n := by
        simp [start]
      have h_stop : start > stop := by
        simp at h_Le
        assumption
      Nat.sliced_indices' h_stop h_start (Nat.succ_pos step)

def Slice.length (s : Slice) (n : ℕ) : ℕ :=
  match s.step with
  | .ofNat step =>
    -- step is nonnegative
    ⌈((Add_Mul_DivSub1Sign_2 n s.stop).toNat.min n - (Add_Mul_DivSub1Sign_2 n s.start).toNat : ℚ) / step⌉.toNat
  | .negSucc step =>
    -- step is negative
    ⌈((Add_Mul_DivSub1Sign_2 n s.start + 1).toNat.min n - (Add_Mul_DivSub1Sign_2 n s.stop + 1).toNat : ℚ) / step.succ⌉.toNat
