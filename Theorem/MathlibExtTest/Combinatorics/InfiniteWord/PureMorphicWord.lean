/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/PureMorphicWord.lean -/


import Mathlib.Tactic
import Def.Combinatorics.InfiniteWord.PureMorphicWord
import Lemma.Finset.InfiniteWord.PureMorphicWord
import Def.MathlibExtTest.Combinatorics.InfiniteWord.PureMorphicWord


namespace MetaMathlibExt

example : morphIterate probeMorphism 0 [false] = [false] := rfl

example : morphIterate probeMorphism 1 [false] = [false, true] := rfl

example : morphIterate probeMorphism 2 [false] = [false, true, true] := rfl

example : IsNonErasing probeMorphism := by intro b; cases b <;> decide

example (n : ℕ) : (morphIterate (fun x : Fin 2 => [x, 1 - x]) n [0]).length = 2 ^ n := by
  rw [morphIterate_length_of_uniform (k := 2) (fun _ => rfl), List.length_singleton, Nat.mul_one]

end MetaMathlibExt
