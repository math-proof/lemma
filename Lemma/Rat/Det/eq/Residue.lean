import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GaloisRep_Adic
import Lemma.Int.P2MUtil


/--
[GaloisRepAdic_det_residual](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_det_residual.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {ρ : GaloisRepAdic A}
-- given
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
-- imply
  LinearMap.det (ρ.residual.ρ σ) = IsLocalRing.residue A (ρ.det σ : A) :=
-- proof
  LinearMap.det_baseChange (ρ.ρ σ)


-- created on 2026-10-23
