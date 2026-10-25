import Def.AutomorphicForm_HeckeEigensystem
import Def.LanglandsTunnell_ExplicitLift
import Instance.LanglandsTunnell_LiftTraceSeed

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2

open NumberField IsDedekindDomain FLT.ExplicitLift

section RelDeg

variable {G : Type*} [Group G] [Finite G] (H : Subgroup G) (σ : G)

theorem exists_pos_pow_mem : ∃ n : ℕ, 0 < n ∧ σ ^ n ∈ H :=
  ⟨orderOf σ, orderOf_pos σ, by rw [pow_orderOf_eq_one]; exact H.one_mem⟩

open Classical in

def relDeg : ℕ := Nat.find (exists_pos_pow_mem H σ)

end RelDeg

section PrimeOver

variable {L : Type*} [Field L] [NumberField L] (H : Subgroup (L ≃ₐ[ℚ] L))

theorem algebraMap_ringOfIntegers_injective :
    Function.Injective (algebraMap (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L)) := by
  intro x y h
  have h' : algebraMap (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) L x
      = algebraMap (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) L y := by
    rw [IsScalarTower.algebraMap_apply (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L) L, h]
  rw [IsScalarTower.algebraMap_apply (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))
      (FixedPoints.intermediateField H : IntermediateField ℚ L) L,
    IsScalarTower.algebraMap_apply (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))
      (FixedPoints.intermediateField H : IntermediateField ℚ L) L] at h'
  exact IsFractionRing.injective (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))
    (FixedPoints.intermediateField H : IntermediateField ℚ L) ((algebraMap _ L).injective h')

theorem exists_prime_over (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))) :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ Q.under (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) = w.asIdeal := by
  haveI := w.isMaximal
  obtain ⟨Q, hQ, hQw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral w.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap_ringOfIntegers_injective H)]; exact bot_le)
  exact ⟨Q, hQ, hQw⟩

def primeOver (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))) : Ideal (𝓞 L) :=
  (exists_prime_over H w).choose

variable (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)))

theorem under_primeOver :
    (primeOver H w).under (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) = w.asIdeal :=
  (exists_prime_over H w).choose_spec.2

theorem primeOver_ne_bot : primeOver H w ≠ ⊥ := fun h => by
  have := under_primeOver H w
  rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _ (algebraMap_ringOfIntegers_injective H)] at this
  exact w.ne_bot this.symm

end PrimeOver

section Frob

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (H : Subgroup (L ≃ₐ[ℚ] L))
  (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)))

def seedFrob : L ≃ₐ[ℚ] L :=
  arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w) ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w))

end Frob

section Seed

def liftOf (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) :=
  Classical.epsilon fun M : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) =>
    M ∈ Submonoid.closure ({Slift, Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))) ∧
      M.map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3))

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (H : Subgroup (L ≃ₐ[ℚ] L))

def liftTraceSeed :
    AutomorphicForm.HeckeEigensystem (FixedPoints.intermediateField H : IntermediateField ℚ L) (ℤ√(-2)) where
  level := ⊤
  level_ne_bot := top_ne_bot
  a := fun w => (liftOf (e (seedFrob H w))).trace
  b := fun w => (liftOf (e (seedFrob H w))).det

end Seed

end LanglandsTunnell.P2

end
