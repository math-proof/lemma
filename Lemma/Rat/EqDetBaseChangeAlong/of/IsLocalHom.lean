import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GaloisRep_Adic
import Lemma.Int.P2MUtil


/--
[GaloisRepAdic_det_baseChangeAlong](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_det_baseChangeAlong.lean)
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
  ((ρ.baseChangeAlong φ hφ).det σ : B) = φ (ρ.det σ : A) := by
-- proof
  letI : Algebra A B := φ.toAlgebra
  show LinearMap.det ((ρ.ρ σ).baseChange B) = φ (LinearMap.det (ρ.ρ σ))
  exact LinearMap.det_baseChange (ρ.ρ σ)


-- created on 2026-10-23
