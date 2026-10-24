import Lemma.Definitions.Def_RatIdele_Normalizer
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.DirichletCharacter.Bounds

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open Rat.HeightOneSpectrum NumberField.AdelicLevel

namespace RatIdele

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

section Residue

def unitPadicAt (p : ℕ) [hp : Fact p.Prime] (x : (𝔸ℚ)ˣ) : ℤ_[p] :=
  (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, hp.out⟩).symm.toAlgEquiv.toRingEquiv
    (unitIntAt ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) x)

theorem unitPadicAt_mul (p : ℕ) [Fact p.Prime] (x y : (𝔸ℚ)ˣ) :
    unitPadicAt p (x * y) = unitPadicAt p x * unitPadicAt p y := by
  unfold unitPadicAt
  rw [unitIntAt_mul, map_mul]

theorem unitPadicAt_one (p : ℕ) [Fact p.Prime] : unitPadicAt p 1 = 1 := by
  unfold unitPadicAt
  rw [unitIntAt_one, map_one]

theorem natCast_mul_unitPadicAt_eq_one (p : ℕ) [hp : Fact p.Prime] {x : (𝔸ℚ)ˣ} {n : ℕ}
    (h : ((n : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩).adicCompletion ℚ)
      * unitAt ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) x = 1) :
    ((n : ℕ) : ℤ_[p]) * unitPadicAt p x = 1 := by
  unfold unitPadicAt
  rw [← map_natCast (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, hp.out⟩).symm.toAlgEquiv.toRingEquiv n,
    ← map_mul, natCast_mul_unitIntAt_eq_one h, map_one]

theorem unitPadicAt_eq_neg_one (p : ℕ) [hp : Fact p.Prime] {x : (𝔸ℚ)ˣ}
    (h : unitAt ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) x = -1) : unitPadicAt p x = -1 := by
  unfold unitPadicAt
  rw [show unitIntAt ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) x = -1 from
    Subtype.ext (by rw [coe_unitIntAt, h, NegMemClass.coe_neg, OneMemClass.coe_one]), map_neg, map_one]

theorem fact_prime_of_mem_primeFactors {N : ℕ} (p : N.primeFactors) : Fact (p : ℕ).Prime :=
  ⟨Nat.prime_of_mem_primeFactors p.2⟩

attribute [local instance] fact_prime_of_mem_primeFactors

variable (N : ℕ)

def unitResidues (x : (𝔸ℚ)ˣ) : (p : N.primeFactors) → ZMod ((p : ℕ) ^ N.factorization p) :=
  fun p => PadicInt.toZModPow (N.factorization p) (unitPadicAt p x)

theorem unitResidues_mul (x y : (𝔸ℚ)ˣ) : unitResidues N (x * y) = unitResidues N x * unitResidues N y := by
  funext p
  show PadicInt.toZModPow (N.factorization p) (unitPadicAt p (x * y))
    = PadicInt.toZModPow (N.factorization p) (unitPadicAt p x)
      * PadicInt.toZModPow (N.factorization p) (unitPadicAt p y)
  rw [unitPadicAt_mul, map_mul]

theorem unitResidues_one : unitResidues N 1 = 1 := by
  funext p
  show PadicInt.toZModPow (N.factorization p) (unitPadicAt p 1) = 1
  rw [unitPadicAt_one, map_one]

variable [NeZero N]

def unitResidue : (𝔸ℚ)ˣ →* ZMod N where
  toFun x := (ZMod.equivPi N (NeZero.ne N)).symm (unitResidues N x)
  map_one' := by rw [unitResidues_one, map_one]
  map_mul' x y := by rw [unitResidues_mul, map_mul]

theorem unitResidue_apply (x : (𝔸ℚ)ˣ) : unitResidue N x = (ZMod.equivPi N (NeZero.ne N)).symm (unitResidues N x) := rfl

theorem equivPi_unitResidue (x : (𝔸ℚ)ˣ) : ZMod.equivPi N (NeZero.ne N) (unitResidue N x) = unitResidues N x := by
  rw [unitResidue_apply, RingEquiv.apply_symm_apply]

theorem natCast_mul_unitResidue_eq_one {x : (𝔸ℚ)ˣ} {n : ℕ}
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), natGenerator w ∣ N → ((n : ℕ) : w.adicCompletion ℚ) * unitAt w x = 1) :
    (n : ZMod N) * unitResidue N x = 1 := by
  apply (ZMod.equivPi N (NeZero.ne N)).injective
  rw [map_mul, map_natCast, equivPi_unitResidue, map_one]
  funext p
  rw [Pi.mul_apply, Pi.natCast_apply, Pi.one_apply]
  show ((n : ℕ) : ZMod ((p : ℕ) ^ N.factorization p)) * PadicInt.toZModPow (N.factorization p) (unitPadicAt p x) = 1
  rw [← map_natCast (PadicInt.toZModPow (p := (p : ℕ)) (N.factorization p)) n, ← map_mul,
    natCast_mul_unitPadicAt_eq_one (p : ℕ) (h _ ?_), map_one]
  rw [natGenerator_primesEquiv_symm]
  exact Nat.dvd_of_mem_primeFactors p.2

theorem unitResidue_eq_one {x : (𝔸ℚ)ˣ} (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), natGenerator w ∣ N → unitAt w x = 1) :
    unitResidue N x = 1 := by
  have := natCast_mul_unitResidue_eq_one N (n := 1) (x := x) fun w hw => by rw [Nat.cast_one, one_mul, h w hw]
  rwa [Nat.cast_one, one_mul] at this

theorem unitResidue_eq_neg_one {x : (𝔸ℚ)ˣ} (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), natGenerator w ∣ N → unitAt w x = -1) :
    unitResidue N x = -1 := by
  apply (ZMod.equivPi N (NeZero.ne N)).injective
  rw [equivPi_unitResidue, map_neg, map_one]
  funext p
  rw [Pi.neg_apply, Pi.one_apply]
  show PadicInt.toZModPow (N.factorization p) (unitPadicAt p x) = -1
  rw [unitPadicAt_eq_neg_one (p : ℕ) (h _ ?_), map_neg, map_one]
  rw [natGenerator_primesEquiv_symm]
  exact Nat.dvd_of_mem_primeFactors p.2

theorem unitResidue_principal (q : ℚˣ) : unitResidue N (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = 1 :=
  unitResidue_eq_one N fun w _ => unitAt_principal w q

end Residue

end RatIdele

namespace DirichletCharacter

open RatIdele

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

def dirichletIdeleChar : (𝔸ℚ)ˣ →* ℂˣ :=
  (χ.toUnitHom.comp (unitResidue N).toHomUnits)⁻¹

theorem coe_dirichletIdeleChar_apply (x : (𝔸ℚ)ˣ) :
    ((dirichletIdeleChar χ x : ℂˣ) : ℂ) = (χ (unitResidue N x))⁻¹ := by
  rw [dirichletIdeleChar, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, MonoidHom.comp_apply, MulChar.coe_toUnitHom,
    MonoidHom.coe_toHomUnits]

theorem dirichletIdeleChar_eq_one_of_unitResidue_eq_one {x : (𝔸ℚ)ˣ} (h : unitResidue N x = 1) :
    dirichletIdeleChar χ x = 1 := by
  refine Units.ext ?_
  rw [coe_dirichletIdeleChar_apply, h, map_one, inv_one, Units.val_one]

theorem dirichletIdeleChar_principal (q : ℚˣ) : dirichletIdeleChar χ (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = 1 :=
  dirichletIdeleChar_eq_one_of_unitResidue_eq_one χ (unitResidue_principal N q)

theorem norm_coe_dirichletIdeleChar_apply (x : (𝔸ℚ)ˣ) : ‖((dirichletIdeleChar χ x : ℂˣ) : ℂ)‖ = 1 := by
  rw [coe_dirichletIdeleChar_apply, norm_inv, ← MonoidHom.coe_toHomUnits (unitResidue N) x, χ.unit_norm_eq_one,
    inv_one]

theorem dirichletIdeleChar_finIncl_localUnit_of_valued_one {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ natGenerator v ∣ N)
    (t : (v.adicCompletion ℚ)ˣ) (ht : Valued.v (t : v.adicCompletion ℚ) = 1) :
    dirichletIdeleChar χ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) = 1 := by
  refine dirichletIdeleChar_eq_one_of_unitResidue_eq_one χ (unitResidue_eq_one N fun w hw => ?_)
  have hwv : w ≠ v := fun h => hv (h ▸ hw)
  unfold unitAt
  rw [ρ_finIncl_localUnit_of_valued_one v t ht, map_one, inv_one, mul_one, Units.coe_map, finIncl_apply_snd,
    localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hwv]

theorem coe_dirichletIdeleChar_finIncl_localUnit_of_valued_exp_neg_one {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ¬ natGenerator v ∣ N) (t : (v.adicCompletion ℚ)ˣ) (ht : Valued.v (t : v.adicCompletion ℚ) = exp (-1 : ℤ)) :
    ((dirichletIdeleChar χ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) : ℂˣ) : ℂ) = χ (natGenerator v) := by
  set x := Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t) with hx
  have hres : ((natGenerator v : ℕ) : ZMod N) * unitResidue N x = 1 := by
    refine natCast_mul_unitResidue_eq_one N fun w hw => ?_
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    unfold unitAt
    rw [ρ_finIncl_localUnit v t ht, hx, Units.coe_map, finIncl_apply_snd, localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hwv,
      one_mul, map_natCast, mul_inv_cancel₀ (natCast_adicCompletion_ne_zero w (prime_natGenerator v).ne_zero)]
  have hχ : χ (natGenerator v) * χ (unitResidue N x) = 1 := by rw [← map_mul, hres, map_one]
  rw [coe_dirichletIdeleChar_apply]
  exact (eq_inv_of_mul_eq_one_left hχ).symm

theorem dirichletIdeleChar_eq_one_of_snd_eq_one_of_pos {x : (𝔸ℚ)ˣ}
    (hx : ∀ w : HeightOneSpectrum (𝓞 ℚ), (x : 𝔸ℚ).2 w = 1) (hpos : 0 < archCoord x) : dirichletIdeleChar χ x = 1 := by
  refine dirichletIdeleChar_eq_one_of_unitResidue_eq_one χ (unitResidue_eq_one N fun w _ => ?_)
  unfold unitAt
  rw [ρ_eq_archSign_of_snd_eq_one hx, archSign, if_pos hpos, hx w, map_one, inv_one, mul_one]

theorem coe_dirichletIdeleChar_of_snd_eq_one_of_neg {x : (𝔸ℚ)ˣ}
    (hx : ∀ w : HeightOneSpectrum (𝓞 ℚ), (x : 𝔸ℚ).2 w = 1) (hneg : archCoord x < 0) :
    ((dirichletIdeleChar χ x : ℂˣ) : ℂ) = χ (-1) := by
  have hres : unitResidue N x = -1 := by
    refine unitResidue_eq_neg_one N fun w _ => ?_
    unfold unitAt
    rw [ρ_eq_archSign_of_snd_eq_one hx, archSign, if_neg (not_lt.mpr hneg.le), hx w, map_neg, map_one, inv_neg,
      inv_one, one_mul]
  have hχ : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [coe_dirichletIdeleChar_apply, hres]
  exact (eq_inv_of_mul_eq_one_left hχ).symm

end DirichletCharacter

end
