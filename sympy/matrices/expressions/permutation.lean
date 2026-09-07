import sympy.functions.special.tensor_functions
import sympy.tensor.stack


/--
Elementary row-shift matrix
delete row `i` and insert after row `j` when `i < j`;
delete row `i` and insert before row `j` when `j < i`.

\[
\det(\mathrm{ShiftMatrix}(n,i,j))=(-1)^{j-i}
\]

(in ℤ; equivalently `(-1)^{|j-i|}`).
-/
def ShiftMatrix [AddMonoidWithOne α] [CharZero α] (n i₀ j₀ : ℕ) : Tensor α [n, n] :=
  [i < n] [j < n]
    if i₀ = j₀ then
      KroneckerDelta i j
    else if i₀ < j₀ then
      if (i : ℕ) = j₀ then
        KroneckerDelta i₀ (j : ℕ)
      else if i₀ ≤ (i : ℕ) ∧ (i : ℕ) < j₀ then
        KroneckerDelta ((i : ℕ) + 1) (j : ℕ)
      else
        KroneckerDelta i j
    else
      if (j : ℕ) = i₀ then
        KroneckerDelta (i : ℕ) j₀
      else if j₀ ≤ (j : ℕ) ∧ (j : ℕ) < i₀ then
        KroneckerDelta (i : ℕ) ((j : ℕ) + 1)
      else
        KroneckerDelta i j


/--
Elementary row-swap matrix

\[
\begin{align*}
&(P)_{i,j}=\delta_{j,i_0}\quad\text{when }i=j_0,\\
&(P)_{i,j}=\delta_{j,j_0}\quad\text{when }i=i_0,\\
&(P)_{i,j}=\delta_{j,i}\quad\text{otherwise.}
\end{align*}
\]
-/
def SwapMatrix [AddMonoidWithOne α] [CharZero α] (n i₀ j₀ : ℕ) : Tensor α [n, n] :=
  [i < n] [j < n]
    if (i : ℕ) = j₀ then
      KroneckerDelta (j : ℕ) i₀
    else if (i : ℕ) = i₀ then
      KroneckerDelta (j : ℕ) j₀
    else
      KroneckerDelta j i


/--
Elementary row-scale matrix

\[
(1+(k-1)\,\delta_{i,i_0})\,\delta_{i,j}
\]

i.e. the identity with the `i₀`-th diagonal entry replaced by `k`.
Determinant: `k`.
-/
def MulMatrix [Ring α] [CharZero α] (n i₀ : ℕ) (k : α) : Tensor α [n, n] :=
  -- `_entry(self, i, j)` with `self.i = i₀`, `self.multiplier = k`
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
