import Def.Data.List.Slice
import Def.Data.List.List.Part4
open Lean


@[simp]
theorem List.length_permute (s : List α) (i : Fin s.length) (d : ℤ) :
    (s.permute i d).length = s.length := by
  unfold List.permute
  split <;> simp [List.slice, List.array_slice] <;> omega

