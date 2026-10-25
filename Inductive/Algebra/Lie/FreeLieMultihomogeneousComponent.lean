import Mathlib.Algebra.Lie.Free


namespace MetaMathlibExt

variable (K : Type) [Field K] {r : ℕ}

/-- A homogeneous Lie monomial in the canonical generators of
`FreeLieAlgebra K (Fin r)`, indexed by its multidegree.

A canonical generator `i` is a monomial whose multidegree is `1` at `i` and
`0` elsewhere; the Lie bracket of monomials of multidegrees `a` and `b` is a
monomial of pointwise multidegree `fun i => a i + b i`. -/
inductive IsFreeLieMonomial : (Fin r → ℕ) → FreeLieAlgebra K (Fin r) → Prop where
  | gen (i : Fin r) :
      IsFreeLieMonomial (Function.update (fun _ => 0) i 1) (FreeLieAlgebra.of K i)
  | bracket {a b : Fin r → ℕ} {x y : FreeLieAlgebra K (Fin r)} :
      IsFreeLieMonomial a x → IsFreeLieMonomial b y →
        IsFreeLieMonomial (fun i => a i + b i) (Bracket.bracket x y)

end MetaMathlibExt
