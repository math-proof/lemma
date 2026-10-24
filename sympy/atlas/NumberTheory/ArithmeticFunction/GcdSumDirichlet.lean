/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/GcdSumDirichlet.lean -/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace MetaMathlibExt

/-! # Dirichlet series of the gcd-sum
-/

private def phiRaw : ℕ → ℂ := fun n => (Nat.totient n : ℂ)

private def idRaw : ℕ → ℂ := fun n => (n : ℂ)

private def gcdRaw : ℕ → ℂ :=
  fun n => ∑ i ∈ Finset.range n, (Nat.gcd n (i + 1) : ℂ)
end MetaMathlibExt
