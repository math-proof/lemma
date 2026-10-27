import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GaloisRep_Adic
import Lemma.Int.P2MUtil

open Polynomial

/--
[GaloisRepAdic_charpoly_residual](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_charpoly_residual.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {ρ : GaloisRepAdic A}
-- given
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
-- imply
  LinearMap.charpoly (ρ.residual.ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map (IsLocalRing.residue A) :=
-- proof
  LinearMap.charpoly_baseChange (ρ.ρ σ) (IsLocalRing.ResidueField A)


-- created on 2026-10-23
