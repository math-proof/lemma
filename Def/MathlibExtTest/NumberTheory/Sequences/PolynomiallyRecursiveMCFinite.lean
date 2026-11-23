/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Sequences/PolynomiallyRecursiveMCFinite.lean -/

module

public import Mathlib.Tactic
public import Def.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite
public import Theorem.Nat.Sequences.PolynomiallyRecursiveMCFinite
public import Theorem.MathlibExtTest.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite

@[expose] public section

namespace MathlibExtTest.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite

open MetaMathlibExt MvPolynomial

/-- `a (n + 1) = a n * b n + n`, `b (n + 1) = b n + 1`, starting from `(1, 1)`. -/
def coupledPair : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | n + 1 => ((coupledPair n).1 * (coupledPair n).2 + n, (coupledPair n).2 + 1)

end MathlibExtTest.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite
