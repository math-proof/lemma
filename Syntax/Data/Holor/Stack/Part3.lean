import Instance.Data.Holor.Tensor.Part2
import Macro.Data.Holor.Stack.Part2
open Lean


/--
Tensor product along axis 0 of a stack: `∏ i < n, f i` means `([i < n] f i).prod 0`.
Uses priority above Mathlib's bounded `∏ i < n, …` (Finset.Iio) notation.
-/
syntax (priority := 10000) "∏ " binderIdent "<" term ", " term:67 : term

