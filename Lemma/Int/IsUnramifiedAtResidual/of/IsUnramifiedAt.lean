import Mathlib
import sympy.Basic
import Def.GaloisRep_Adic
import Lemma.Int.P2MUtil


/--
[GaloisRepAdic_isUnramifiedAt_residual](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_isUnramifiedAt_residual.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {ρ : GaloisRepAdic A}
  {q : ℕ}
-- given
  (h : ρ.IsUnramifiedAt q) :
-- imply
  ρ.residual.IsUnramifiedAt q := by
-- proof
  intro P hP σ hσ
  show (ρ.ρ σ).baseChange (IsLocalRing.ResidueField A) = 1
  rw [h P hP σ hσ, LinearMap.baseChange_one]


-- created on 2026-10-23
