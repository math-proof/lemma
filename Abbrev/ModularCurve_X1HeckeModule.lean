module
public import Theorem.LaurentSeries.X1HeckeOperator
public import Def.ModularCurve_X1Diamond
public import Abbrev.ModularCurve_JZeroTateModule
public import Mathlib.Algebra.MvPolynomial.CommRing
set_option autoImplicit false


public section

noncomputable section

open scoped TensorProduct

namespace ModularCurve

open AlgebraicCurve

abbrev HeckeAlgOne : Type := MvPolynomial (Nat.Primes ⊕ ℕ) ℤ

section Operators

variable (M : ℕ)

end Operators

section Eval

variable {M : ℕ}

end Eval

section TheModule

variable (M : ℕ)

end TheModule

section Integral

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]

end Integral

section Rational

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]

end Rational

section Predicate

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]
  [DistribMulAction (L ≃ₐ[K] L) J]

end Predicate

section ModularInstance

end ModularInstance

end ModularCurve

end
