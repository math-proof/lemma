import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GaloisRep_Adic
import Lemma.Int.P2MUtil


/--
[GaloisRepAdic_trace_baseChangeAlong](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_trace_baseChangeAlong.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  {φ : A →+* B}
  {ρ : GaloisRepAdic A}
-- given
  (hφ : IsLocalHom φ)
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
-- imply
  (ρ.baseChangeAlong φ hφ).trace σ = φ (ρ.trace σ) := by
-- proof
  letI : Algebra A B := φ.toAlgebra
  exact LinearMap.trace_baseChange (ρ.ρ σ) B


-- created on 2026-10-23
