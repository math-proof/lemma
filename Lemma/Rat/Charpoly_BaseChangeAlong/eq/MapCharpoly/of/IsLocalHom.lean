import Mathlib
import sympy.Basic
import Def.GaloisRep_Adic
import Lemma.Int.P2MUtil

open Polynomial

/--
[GaloisRepAdic_charpoly_baseChangeAlong](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_charpoly_baseChangeAlong.lean)
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
  LinearMap.charpoly ((ρ.baseChangeAlong φ hφ).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map φ := by
-- proof
  letI : Algebra A B := φ.toAlgebra
  exact LinearMap.charpoly_baseChange (ρ.ρ σ) B


-- created on 2026-10-23
