import Def.Analysis.SpecialFunctions.TensorFunctions
import Def.Data.Tensor.Stack.Part2


/--
Elementary row-scale matrix

\[
(1+(k-1)\,\delta_{i,i_0})\,\delta_{i,j}
\]

i.e. the identity with the `i₀`-th diagonal entry replaced by `k`.
Determinant: `k`.
-/
def MulMatrix [Ring α] [CharZero α] (n i₀ : ℕ) (k : α) : Tensor α [n, n] :=
  [i < n] [j < n]
    (1 + (k - 1) * KroneckerDelta (i : ℕ) i₀) * KroneckerDelta i j


/--
Elementary row-add matrix

multiply the `i₀`-th row by `k` and add it to the `j₀`-th row
(left-multiplication); equivalently for columns on the right.
-/
def AddMatrix [Ring α] [CharZero α] (n i₀ j₀ : ℕ) (k : α := 1) : Tensor α [n, n] :=
  [i < n] [j < n]
    if i₀ = j₀ then
      KroneckerDelta j i
    else if (i : ℕ) = j₀ then
      if (j : ℕ) = i₀ then
        k
      else
        KroneckerDelta (j : ℕ) j₀
    else
      KroneckerDelta j i
