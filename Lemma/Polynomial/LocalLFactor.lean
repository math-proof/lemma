import Mathlib
import Def.AutomorphicForm_HeckeEigensystem
import Theorems.Thm_AutomorphicForm_satakePow_add_pow
import Def.AutomorphicForm_LocalLFactor

set_option autoImplicit false

open IsDedekindDomain NumberField Polynomial

noncomputable section

namespace AutomorphicForm

@[simp] theorem satakePow_two {R : Type*} [CommRing R] (s e : R) :
    satakePow 2 s e = s ^ 2 - 2 * e := by
  show s * s - e * 2 = s ^ 2 - 2 * e; ring

variable {R : Type*} [CommRing R]


@[simp] theorem heckeLFactorPoly_def (s e : R) :
    heckeLFactorPoly s e = 1 - C s * X + C e * X ^ 2 := rfl

@[simp] theorem coeff_zero_heckeLFactorPoly (s e : R) :
    (heckeLFactorPoly s e).coeff 0 = 1 := by
  simp [heckeLFactorPoly, coeff_one, coeff_X_pow]

@[simp] theorem coeff_one_heckeLFactorPoly (s e : R) :
    (heckeLFactorPoly s e).coeff 1 = -s := by
  simp [heckeLFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

@[simp] theorem coeff_two_heckeLFactorPoly (s e : R) :
    (heckeLFactorPoly s e).coeff 2 = e := by
  simp [heckeLFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

theorem heckeLFactorPoly_inj {s e s' e' : R}
    (h : heckeLFactorPoly s e = heckeLFactorPoly s' e') : s = s' ∧ e = e' := by
  refine ⟨?_, ?_⟩
  · have h1 := congrArg (fun p => p.coeff 1) h
    simp only [coeff_one_heckeLFactorPoly] at h1
    exact neg_injective h1
  · have h2 := congrArg (fun p => p.coeff 2) h
    simpa only [coeff_two_heckeLFactorPoly] using h2

theorem heckeLFactorPoly_eq_iff {s e s' e' : R} :
    heckeLFactorPoly s e = heckeLFactorPoly s' e' ↔ s = s' ∧ e = e' :=
  ⟨heckeLFactorPoly_inj, fun ⟨hs, he⟩ => by rw [hs, he]⟩

theorem heckeLFactorPoly_split (α β : R) :
    heckeLFactorPoly (α + β) (α * β) = (1 - C α * X) * (1 - C β * X) := by
  simp only [heckeLFactorPoly, map_add, map_mul]
  ring

theorem map_heckeLFactorPoly {S : Type*} [CommRing S] (φ : R →+* S) (s e : R) :
    (heckeLFactorPoly s e).map φ = heckeLFactorPoly (φ s) (φ e) := by
  simp [heckeLFactorPoly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_one, Polynomial.map_pow, map_C, map_X]


@[simp] theorem HeckeEigensystem.localLFactor_def {F : Type*} [Field F] [NumberField F]
    (π : HeckeEigensystem F R) (v : HeightOneSpectrum (𝓞 F)) :
    π.localLFactor v = heckeLFactorPoly (π.a v) (π.b v) := rfl

theorem HeckeEigensystem.satake_eq_of_localLFactor_eq {F : Type*} [Field F] [NumberField F]
    {π π' : HeckeEigensystem F R} {v : HeightOneSpectrum (𝓞 F)}
    (h : π.localLFactor v = π'.localLFactor v) : π.a v = π'.a v ∧ π.b v = π'.b v :=
  heckeLFactorPoly_inj h

section Factoring

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]

theorem isBaseChangeAt_iff_localLFactor (π : HeckeEigensystem E R) (Φ : HeckeEigensystem L R)
    (𝔓 : HeightOneSpectrum (𝓞 L)) :
    IsBaseChangeAt π Φ 𝔓 ↔
      Φ.localLFactor 𝔓 =
        heckeLFactorPoly
          (satakePow ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)
            (π.a (𝔓.under (𝓞 E))) (π.b (𝔓.under (𝓞 E))))
          ((π.b (𝔓.under (𝓞 E))) ^ ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)) := by
  unfold IsBaseChangeAt HeckeEigensystem.localLFactor
  exact heckeLFactorPoly_eq_iff.symm

theorem isBaseChangeOf_iff_localLFactor (π : HeckeEigensystem E R)
    (Φ : HeckeEigensystem L R) :
    IsBaseChangeOf π Φ ↔
      ∃ S : Finset (HeightOneSpectrum (𝓞 L)), ∀ 𝔓 ∉ S,
        Φ.localLFactor 𝔓 =
          heckeLFactorPoly
            (satakePow ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)
              (π.a (𝔓.under (𝓞 E))) (π.b (𝔓.under (𝓞 E))))
            ((π.b (𝔓.under (𝓞 E))) ^
              ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)) := by
  unfold IsBaseChangeOf
  refine exists_congr fun S => forall_congr' fun 𝔓 => forall_congr' fun _ => ?_
  exact isBaseChangeAt_iff_localLFactor π Φ 𝔓

theorem agreesAwayFromFinite_iff_localLFactor {F : Type*} [Field F] [NumberField F]
    (π π' : HeckeEigensystem F R) :
    HeckeEigensystem.AgreesAwayFromFinite π π' ↔
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        π.localLFactor v = π'.localLFactor v := by
  unfold HeckeEigensystem.AgreesAwayFromFinite
  refine exists_congr fun S => forall_congr' fun v => forall_congr' fun _ => ?_
  exact heckeLFactorPoly_eq_iff.symm

end Factoring

theorem heckeLFactorPoly_satakePow_split (f : ℕ) (α β : R) :
    heckeLFactorPoly (satakePow f (α + β) (α * β)) ((α * β) ^ f)
      = (1 - C (α ^ f) * X) * (1 - C (β ^ f) * X) := by
  rw [satakePow_add_pow, mul_pow, heckeLFactorPoly_split]

theorem heckeLFactorPoly_satakePow_one (s e : R) :
    heckeLFactorPoly (satakePow 1 s e) (e ^ 1) = heckeLFactorPoly s e := by
  rw [satakePow_one, pow_one]

theorem heckeLFactorPoly_satakePow_two (s e : R) :
    heckeLFactorPoly (satakePow 2 s e) (e ^ 2)
      = 1 - C (s ^ 2 - 2 * e) * X + C (e ^ 2) * X ^ 2 := by
  rw [satakePow_two, heckeLFactorPoly]

section ConductorCarrier

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]


omit [Algebra.IsIntegral (𝓞 E) (𝓞 L)] in

theorem hasBaseChangeLevelLaw_sat (π : HeckeEigensystem E R)
    (Φ : HeckeEigensystem L R) : HasBaseChangeLevelLaw Φ.level π Φ :=
  dvd_mul_right Φ.level (Ideal.map (algebraMap (𝓞 E) (𝓞 L)) π.level)

theorem isBaseChangeOf_and_hasBaseChangeLevelLaw_iff (𝔡 : Ideal (𝓞 L))
    (π : HeckeEigensystem E R) (Φ : HeckeEigensystem L R) :
    (IsBaseChangeOf π Φ ∧ HasBaseChangeLevelLaw 𝔡 π Φ) ↔
      ((∃ S : Finset (HeightOneSpectrum (𝓞 L)), ∀ 𝔓 ∉ S,
          Φ.localLFactor 𝔓 =
            heckeLFactorPoly
              (satakePow ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)
                (π.a (𝔓.under (𝓞 E))) (π.b (𝔓.under (𝓞 E))))
              ((π.b (𝔓.under (𝓞 E))) ^
                ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal))) ∧
        Φ.level ∣ 𝔡 * Ideal.map (algebraMap (𝓞 E) (𝓞 L)) π.level) :=
  and_congr (isBaseChangeOf_iff_localLFactor π Φ) Iff.rfl

end ConductorCarrier

end AutomorphicForm

end
