import sympy.functions.special.tensor_functions
import sympy.tensor.stack


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


def Fin.shiftRow {n : ℕ} (i i₀ j₀ : Fin n) : Fin n :=
  if i = j₀ then
    i₀
  else if h : i ∈ Ioc j₀ i₀ then
    ⟨i - 1, by grind⟩
  else if h : i ∈ Ico i₀ j₀ then
    ⟨i + 1, by grind⟩
  else
    i


/--
Translation `x ↦ x + i` on `Fin n`.
-/
def Fin.addRight {n : ℕ} (i : Fin n) : Equiv (Fin n) (Fin n) where
  toFun x := x + i
  invFun y := ⟨((y : ℕ) + n - (i : ℕ)) % n, Nat.mod_lt _ (Fin.pos i)⟩
  left_inv x := by
    apply Fin.ext
    show (((x : ℕ) + (i : ℕ)) % n + n - (i : ℕ)) % n = (x : ℕ)
    have hx : (x : ℕ) < n := x.isLt
    have hi : (i : ℕ) < n := i.isLt
    have hmod1 : ∀ (a : ℕ), a < n → (a + n) % n = a := by
      intro a ha
      have key : (a + n) % n = a % n := by
        have e : a + n = a + n * 1 := by simp
        rw [e, Nat.add_mul_mod_self_left]
      exact key.trans (Nat.mod_eq_of_lt ha)
    by_cases h : (x : ℕ) + (i : ℕ) < n
    · rw [Nat.mod_eq_of_lt h]
      have h2 : (x : ℕ) + (i : ℕ) + n - (i : ℕ) = x + n := by omega
      rw [h2]
      exact hmod1 x hx
    · have h' : n ≤ (x : ℕ) + (i : ℕ) := by omega
      have hlt : (x : ℕ) + (i : ℕ) - n < n := by omega
      have hsub : (x : ℕ) + (i : ℕ) = n + ((x : ℕ) + (i : ℕ) - n) :=
        (Nat.add_sub_of_le h').symm
      have hm : ((x : ℕ) + (i : ℕ)) % n = (x : ℕ) + (i : ℕ) - n := by
        conv_lhs => rw [hsub, Nat.add_comm]
        exact hmod1 ((x : ℕ) + (i : ℕ) - n) hlt
      rw [hm]
      have h3 : (x : ℕ) + (i : ℕ) - n + n - (i : ℕ) = x := by omega
      rw [h3]
      exact Nat.mod_eq_of_lt hx
  right_inv y := by
    apply Fin.ext
    show (((y : ℕ) + n - (i : ℕ)) % n + (i : ℕ)) % n = (y : ℕ)
    have hy : (y : ℕ) < n := y.isLt
    have hi : (i : ℕ) < n := i.isLt
    have hmod1 : ∀ (a : ℕ), a < n → (a + n) % n = a := by
      intro a ha
      have key : (a + n) % n = a % n := by
        have e : a + n = a + n * 1 := by simp
        rw [e, Nat.add_mul_mod_self_left]
      exact key.trans (Nat.mod_eq_of_lt ha)
    rw [Nat.mod_add_mod]
    have h : (y : ℕ) + n - (i : ℕ) + (i : ℕ) = y + n := by omega
    rw [h]
    exact hmod1 y hy


/--
Elementary row-shift matrix
delete row `i` and insert after row `j` when `i < j`;
delete row `i` and insert before row `j` when `j < i`.

`(P)_{i,j} = δ(i.shiftRow i₀ j₀, j)`; out-of-range `i₀`, `j₀` are reduced modulo `n`.

\[
\det(\mathrm{ShiftMatrix}(n,i,j))=(-1)^{j-i}
\]

(in ℤ; equivalently `(-1)^{|j-i|}`).
-/
def ShiftMatrix [AddMonoidWithOne α] [CharZero α] (n i₀ j₀ : ℕ) : Tensor α [n, n] :=
  [i < n] [j < n] KroneckerDelta (i.shiftRow ⟨i₀ % n, Nat.mod_lt i₀ (Fin.pos i)⟩ ⟨j₀ % n, Nat.mod_lt j₀ (Fin.pos i)⟩) j


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
