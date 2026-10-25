/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/Tribonacci.lean -/


import Def.Combinatorics.InfiniteWord.Tribonacci.Part2
import Lemma.Finset.InfiniteWord.Tribonacci


namespace InfiniteWord

example : tribonacciWordApprox 0 = [.a] :=
  rfl

example : tribonacciWordApprox 1 = [.a, .b] :=
  rfl

example : tribonacciWordApprox 2 = [.a, .b, .a, .c] :=
  rfl

/-- The recurrence forces `W(3) = abacaba`. -/
example : tribonacciWordApprox 3 = [.a, .b, .a, .c, .a, .b, .a] :=
  rfl

/-- The string printed as `W(3)` in the source is `W(4)` under its recurrence. -/
example : tribonacciWordApprox 4 =
    [.a, .b, .a, .c, .a, .b, .a, .a, .b, .a, .c, .a, .b] :=
  rfl

example : tribonacciWordApprox 3 =
    tribonacciWordApprox 2 ++ tribonacciWordApprox 1 ++ tribonacciWordApprox 0 :=
  tribonacciWordApprox_add_three 0

example : List.IsPrefix (tribonacciWordApprox 2) (tribonacciWordApprox 3) :=
  tribonacciWordApprox_prefix_succ 2

/-- A later approximant agrees with the infinite word at a shared position. -/
example : (tribonacciWordApprox 4)[2]'(by decide) = tribonacciWord 2 :=
  tribonacciWord_eq_getElem_of_le 2 4 (by decide) (by decide)

example :
    tribonacciWord 0 = .a ∧ tribonacciWord 1 = .b ∧
      tribonacciWord 2 = .a ∧ tribonacciWord 3 = .c :=
  ⟨rfl, rfl, rfl, rfl⟩

end InfiniteWord
