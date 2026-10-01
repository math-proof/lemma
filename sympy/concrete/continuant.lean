import sympy.Basic

/-!
Continuants behind SymPy's `K(x[:n])` and `H(x[:n])` (`Lemma/Finset/K/eq/Add/definition.py`,
`Lemma/Finset/H/eq/Add/definition.py`), indexed by the slice length `n`, over any commutative ring.
py: `K(x[:1]) = 1`, `K(x[:2]) = x[1]`, `K(x[:n]) = K(x[:n-1]) * x[n-1] + K(x[:n-2])`;
`H(x[:1]) = x[0]`, `H(x[:2]) = x[1] * x[0] + 1`, `H(x[:n]) = H(x[:n-1]) * x[n-1] + H(x[:n-2])`.
The length-0 values `K 0 = 0`, `H 0 = 1` are the unique ones making the recurrence hold from `n = 2`.
-/

namespace Continuant

variable {R : Type*} [CommRing R]

def K (x : ℕ → R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n + 2 => K x (n + 1) * x (n + 1) + K x n

def H (x : ℕ → R) : ℕ → R
  | 0 => 1
  | 1 => x 0
  | n + 2 => H x (n + 1) * x (n + 1) + H x n

theorem K_two (x : ℕ → R) : K x 2 = x 1 := by
  simp [K]

theorem H_two (x : ℕ → R) : H x 2 = x 1 * x 0 + 1 := by
  simp only [H]
  ring

end Continuant
