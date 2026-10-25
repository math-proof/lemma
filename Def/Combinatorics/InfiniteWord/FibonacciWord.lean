/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean -/

import Mathlib.Data.List.Defs


namespace MetaMathlibExt

/-- Binary Fibonacci substitution on letters, `0` maps to `01` and `1` maps to `0`.
Letters `0` and `1` are represented by `false` and `true`.
Concept `jis_sem_f409ef3715730614fd194b4d`, source `jis_2ff564e576beedc024b95b9a`. -/
def fibSubst : Bool → List Bool
  | false => [false, true]
  | true => [false]

/-- Extension of the Fibonacci substitution to finite words by concatenation.
Concept `jis_sem_f409ef3715730614fd194b4d`, source `jis_2ff564e576beedc024b95b9a`. -/
def fibMorph : List Bool → List Bool
  | [] => []
  | b :: w => fibSubst b ++ fibMorph w

/-- Finite Fibonacci iterates starting at the one-letter word `0`.
The source displays `0`, `01`, `010`, `01001`, `01001010`, and so on.
Concept `jis_sem_f409ef3715730614fd194b4d`, source `jis_2ff564e576beedc024b95b9a`. -/
def fibWord : ℕ → List Bool
  | 0 => [false]
  | n + 1 => fibMorph (fibWord n)

/-- One-sided infinite Fibonacci word as the pointwise limit of the nested
finite iterates. Index `n` is read from the finite iterate at depth `n + 2`.
Concept `jis_sem_f409ef3715730614fd194b4d`, sources `jis_138e7e26819c0bf6a015b5e7`,
`jis_52830047049fa91220ac91eb`, `jis_2ff564e576beedc024b95b9a`. -/
def fibInf (n : ℕ) : Bool :=
  (fibWord (n + 2)).getD n false

end MetaMathlibExt
