/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KPerfect.lean -/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Def.NumberTheory.KPerfect
/-!
# Parameterized perfect numbers

A positive natural number `n` is `k`-perfect when its sum of positive divisors is `k * n`.

## References

* Yoshinosuke Hirakawa, *A note on the Diophantine equation
  2ℓn² = 1 + q + ⋯ + q^α and application to odd perfect numbers*, arXiv:2309.17084v3
-/

@[expose] public section

namespace Nat

instance decidableIsKPerfect (k n : ℕ) : Decidable (IsKPerfect k n) := by
  unfold IsKPerfect
  infer_instance

end Nat
