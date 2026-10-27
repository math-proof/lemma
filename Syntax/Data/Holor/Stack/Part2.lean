import Instance.Data.Holor.Tensor.Part2
import Macro.Data.Holor.Stack
open Lean


/--
Tensor sum along axis 0 of a stack: `∑ i < n, f i` means `([i < n] f i).sum 0`.
Uses priority above Mathlib's bounded `∑ i < n, …` (Finset.Iio) notation.
-/
syntax (priority := 10000) "∑ " binderIdent "<" term ", " term:67 : term

