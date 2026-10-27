import Mathlib
import Initialize.Tactic.Attr.Basic
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
open ValuationSubring
open scoped Pointwise


/-- ported from external source -/

private lemma residue_eq_one_of_pow_prime_pow_eq_one
  (P : ValuationSubring (AlgebraicClosure ℚ))
  {p : ℕ} (hp : p.Prime) (hP : P.LiesOverPrime p)
  {ζ : AlgebraicClosure ℚ} {n : ℕ} (hζ : ζ ^ p ^ n = 1) (hζP : ζ ∈ P) :
  IsLocalRing.residue P ⟨ζ, hζP⟩ = 1 := by
  have := Fact.mk hp
  have hP' : ((p : ℕ) : AlgebraicClosure ℚ) ∈ P.nonunits := hP
  have hpP : ((p : ℕ) : P) ∈ IsLocalRing.maximalIdeal P := by
    rwa [← coe_mem_nonunits_iff, SubringClass.coe_natCast]
  have hchar : CharP (IsLocalRing.ResidueField P) p := by
    rwa [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (IsLocalRing.residue P), IsLocalRing.residue_eq_zero_iff]
  have hx : (⟨ζ, hζP⟩ : P) ^ p ^ n = 1 := Subtype.ext (by simp only [SubmonoidClass.coe_pow]; exact hζ)
  have hrp : IsLocalRing.residue P ⟨ζ, hζP⟩ ^ p ^ n = 1 := by
    rw [← map_pow, hx, map_one]
  have h0 : (IsLocalRing.residue P ⟨ζ, hζP⟩ - 1) ^ p ^ n = 0 := by
    rw [sub_pow_char_pow, hrp, one_pow, sub_self]
  refine sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero n hp.ne_zero)).mp h0)
@[path]
private lemma main
  {P : ValuationSubring (AlgebraicClosure ℚ)}
  {p : ℕ}
  {ζ : AlgebraicClosure ℚ}
  {n : ℕ}
-- given
  (hp : p.Prime)
  (hP : P.LiesOverPrime p)
  (hζ : ζ ^ p ^ n = 1)
  (hζP : ζ ∈ P) :
-- imply
  IsLocalRing.residue P ⟨ζ, hζP⟩ = 1 :=
-- proof
  residue_eq_one_of_pow_prime_pow_eq_one P hp hP hζ hζP


-- created on 2026-10-23
