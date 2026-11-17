/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/GcdSumDirichlet.lean -/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Dirichlet

@[expose] public section

namespace MetaMathlibExt

/-! # Dirichlet series of the gcd-sum
-/

def phiRaw : ℕ → ℂ := fun n => (Nat.totient n : ℂ)

def idRaw : ℕ → ℂ := fun n => (n : ℂ)

def gcdRaw : ℕ → ℂ :=
  fun n => ∑ i ∈ Finset.range n, (Nat.gcd n (i + 1) : ℂ)

end MetaMathlibExt
