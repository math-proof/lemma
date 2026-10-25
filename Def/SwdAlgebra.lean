import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Span.Defs

set_option autoImplicit false

namespace SwdAlgebra

noncomputable def qP (F : Type) [Field F] : PowerSeries F :=
  PowerSeries.map (Int.castRingHom F)
    (PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ))

noncomputable def qE4 (F : Type) [Field F] : PowerSeries F :=
  PowerSeries.map (Int.castRingHom F)
    (PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3)

noncomputable def qE6 (F : Type) [Field F] : PowerSeries F :=
  PowerSeries.map (Int.castRingHom F)
    (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5)

noncomputable def swdSpan (F : Type) [Field F] (n : ℤ) : Submodule F (PowerSeries F) :=
  Submodule.span F {ψ | ∃ a b : ℕ, (4 * a + 6 * b : ℤ) = n ∧ ψ = qE4 F ^ a * qE6 F ^ b}

noncomputable def ev (F : Type) [Field F] : MvPolynomial (Fin 2) F →ₐ[F] PowerSeries F :=
  MvPolynomial.aeval ![qE4 F, qE6 F]

noncomputable def sD (F : Type) [Field F] :
    Derivation F (MvPolynomial (Fin 2) F) (MvPolynomial (Fin 2) F) :=
  (MvPolynomial.C (-4 : F) * MvPolynomial.X 1 : MvPolynomial (Fin 2) F) • MvPolynomial.pderiv 0 +
    (MvPolynomial.C (-6 : F) * MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 2) F) • MvPolynomial.pderiv 1

end SwdAlgebra
