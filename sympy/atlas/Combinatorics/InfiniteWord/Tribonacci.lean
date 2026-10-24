/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean -/

import Mathlib.Data.List.Basic

/-!
# The Tribonacci word

This file constructs the finite Tribonacci words and their coherent infinite limit.

The source prints `W(3) = abacabaabacab`, but its stated recurrence makes this word
`W(4)` and gives `W(3) = abacaba`; the definitions below follow the recurrence.

## References

- [E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
  Tribonacci Numbers*](https://cs.uwaterloo.ca/journals/JIS/VOL28/Khovanova/khova43.tex),
  Section 5.1 (source statement `jis_e3c891cabe6bea6b4eecdf73`).
-/

namespace InfiniteWord

/-- The three-letter alphabet of the Tribonacci word. -/
inductive TribonacciLetter : Type
  | a : TribonacciLetter
  | b : TribonacciLetter
  | c : TribonacciLetter
  deriving DecidableEq, Repr, Inhabited

/-- Finite Tribonacci-word approximants: `W(0) = a`, `W(1) = ab`, `W(2) = abac`,
and `W(n + 3) = W(n + 2) W(n + 1) W(n)`, where juxtaposition is concatenation. -/
def tribonacciWordApprox : Nat → List TribonacciLetter
  | 0 => [.a]
  | 1 => [.a, .b]
  | 2 => [.a, .b, .a, .c]
  | n + 3 => tribonacciWordApprox (n + 2) ++ tribonacciWordApprox (n + 1) ++
      tribonacciWordApprox n

/-- The defining recursion for finite Tribonacci-word approximants. -/
theorem tribonacciWordApprox_add_three (n : Nat) :
    tribonacciWordApprox (n + 3) =
      tribonacciWordApprox (n + 2) ++ tribonacciWordApprox (n + 1) ++
        tribonacciWordApprox n :=
  rfl

/-- The lengths satisfy the corresponding Tribonacci recurrence. -/
theorem tribonacciWordApprox_length_add_three (n : Nat) :
    (tribonacciWordApprox (n + 3)).length =
      (tribonacciWordApprox (n + 2)).length +
        (tribonacciWordApprox (n + 1)).length + (tribonacciWordApprox n).length := by
  simp only [tribonacciWordApprox_add_three, List.length_append, Nat.add_assoc]

/-- Every finite Tribonacci-word approximant is longer than its index. -/
theorem tribonacciWordApprox_length_ge (n : Nat) :
    n + 1 ≤ (tribonacciWordApprox n).length := by
  have haux : ∀ m : Nat,
      m + 1 ≤ (tribonacciWordApprox m).length ∧
        m + 2 ≤ (tribonacciWordApprox (m + 1)).length ∧
          m + 3 ≤ (tribonacciWordApprox (m + 2)).length := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      obtain ⟨h₀, h₁, h₂⟩ := ih
      refine ⟨h₁, h₂, ?_⟩
      have hidx : m + 1 + 2 = m + 3 := by omega
      rw [hidx, tribonacciWordApprox_length_add_three m]
      omega
  exact (haux n).1

/-- Each finite Tribonacci-word approximant is a prefix of the next one. -/
theorem tribonacciWordApprox_prefix_succ : ∀ n : Nat,
    List.IsPrefix (tribonacciWordApprox n) (tribonacciWordApprox (n + 1))
  | 0 => ⟨[.b], rfl⟩
  | 1 => ⟨[.a, .c], rfl⟩
  | n + 2 => by
    have hidx : n + 2 + 1 = n + 3 := by omega
    rw [hidx, tribonacciWordApprox_add_three n, List.append_assoc]
    exact List.prefix_append _ _

/-- The infinite Tribonacci word, obtained from the coherent chain of finite approximants. -/
def tribonacciWord (k : Nat) : TribonacciLetter :=
  (tribonacciWordApprox k)[k]'(by
    have h := tribonacciWordApprox_length_ge k
    omega)
end InfiniteWord
