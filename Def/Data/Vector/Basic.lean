module

public import Mathlib.Data.Vector.MapLemmas
public import Theorem.List.LengthRange.eq.Length
public import Def.Data.List.List.Basic

@[expose] public section
open Nat Lean


namespace List.Vector

def sum [Add α] [Zero α] : Vector α n → α
  | ⟨v, _⟩ => v.sum

def prod [Mul α] [One α] : Vector α n → α
  | ⟨v, _⟩ => v.prod

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
  ⟨s.range n, LengthRange.eq.Length (s := s) (n := n)⟩

def flatten (xs : Vector (Vector α n) m) : Vector α (m * n) :=
  ⟨(xs.toList.map Vector.toList).flatten, by simp_all [Function.comp_def, List.map_const']⟩

def array_slice (L : Vector α n) (start : Nat) (step : Nat) : Vector α (min step (n - start)) :=
  (take step ∘ drop start) L

def unflatten (xs : Vector α (m * n)) : Vector (Vector α n) m :=
  (range m).map fun i : Fin m =>
    -- Inline of Nat.EqMin_SubMulS: that Theorem module and
    -- Theorem.List.LengthRange.eq.Length both export a public `left`.
    cast (by
      rw [Nat.mul_comm m n, Nat.mul_comm (i : ℕ) n, ← Nat.mul_sub_left_distrib]
      rw [Nat.min_eq_left (Nat.le_mul_of_pos_right n (Nat.sub_pos_of_lt i.isLt))])
      (xs.array_slice (i * n) n)

/--
Python-like slicing operator for List/Vector
useage examples:
```lean
def s : List ℕ := List.range 10
-- def s : List.Vector (Fin 10) 10 := List.Vector.range 10
#eval s[-1:-1:-1]   -- []
#eval s[-1:-10:-1]  -- [9, 8, 7, 6, 5, 4, 3, 2, 1]
#eval s[9:0:-1]     -- [9, 8, 7, 6, 5, 4, 3, 2, 1]
#eval s[-10:-11:-1] -- [0]
#eval s[0:-1:-1]    -- []
#eval s[-20:-9]     -- [0]
#eval s[1:-2:5]     -- [1, 6]
#eval s[0:9:2]      -- [0, 2, 4, 6, 8]
#eval s[-2:0:-2]    -- [8, 6, 4, 2]
#eval s[-2:]        -- [8, 9]
#eval s[-2::-2]     -- [8, 6, 4, 2, 0]
#eval s[2::2]       -- [2, 4, 6, 8]
#eval s[::3]        -- [0, 3, 6, 9]
#eval s[::-3]       -- [9, 6, 3, 0]
```
-/
def getSlice (L : Vector α n) (s : Slice) : Vector α (s.length n) :=
  (indices s L.length).map fun i => L[i]

/-- Infoview: reverse `getSlice` to Python slice syntax. -/
@[app_unexpander getSlice]
meta def getSlice.unexpand := Slice.getSliceUnexpand

end List.Vector
