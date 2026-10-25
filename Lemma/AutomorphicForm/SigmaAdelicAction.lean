import Def.M4aHerbrand_IdeleClassVocab
import Def.AutomorphicForm_SigmaAdelicAction

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

variable (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E)


theorem sigmaAdelicAct_one : sigmaAdelicAct F E D 1 = MonoidHom.id _ := by
  ext g i j
  show ((D.act 1 : RingAut _).toRingHom : AdeleRing (𝓞 E) E → _) (g.val i j) = g.val i j
  rw [D.act.map_one]
  rfl

theorem sigmaAdelicAct_mul (σ τ : E ≃ₐ[F] E) :
    sigmaAdelicAct F E D (σ * τ) = (sigmaAdelicAct F E D σ).comp (sigmaAdelicAct F E D τ) := by
  ext g i j
  show ((D.act (σ * τ) : RingAut _).toRingHom : AdeleRing (𝓞 E) E → _) (g.val i j) =
    ((D.act σ : RingAut _).toRingHom : _ → _)
      (((D.act τ : RingAut _).toRingHom : _ → _) (g.val i j))
  rw [D.act.map_mul]
  rfl

theorem continuous_sigmaAdelicAct (σ : E ≃ₐ[F] E) :
    Continuous (sigmaAdelicAct F E D σ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Continuous.matrix_map (Units.continuous_val) (D.continuous_act σ)
  · exact Continuous.matrix_map (Units.continuous_coe_inv) (D.continuous_act σ)

theorem sigmaAdelicAct_globalPoints (σ : E ≃ₐ[F] E)
    (g : Matrix.GeneralLinearGroup (Fin 2) E) :
    sigmaAdelicAct F E D σ
        (Matrix.GeneralLinearGroup.map (algebraMap E (AdeleRing (𝓞 E) E)) g) =
      Matrix.GeneralLinearGroup.map (algebraMap E (AdeleRing (𝓞 E) E))
        (Matrix.GeneralLinearGroup.map (σ : E →+* E) g) := by
  ext i j
  exact D.compat σ (g.val i j)

theorem sigmaSectionActOn_one
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) → ℂ) :
    sigmaSectionActOn F E D 1 φ = φ := by
  ext g
  show φ (sigmaAdelicAct F E D 1 g) = φ g
  rw [sigmaAdelicAct_one]
  rfl

theorem sigmaPairingOn_one
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E))]
    (νK : MeasureTheory.Measure (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E)))
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) → ℂ) :
    sigmaPairingOn F E D νK 1 φ = ∫ k, φ k * starRingEnd ℂ (φ k) ∂νK := by
  unfold sigmaPairingOn
  rw [sigmaSectionActOn_one]

theorem sigmaPairingOn_zero
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E))]
    (νK : MeasureTheory.Measure (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E)))
    (σ : E ≃ₐ[F] E) :
    sigmaPairingOn F E D νK σ 0 = 0 := by
  unfold sigmaPairingOn
  simp only [Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]

section Inhabitant

example :
    haveI : Subsingleton (ℚ ≃ₐ[ℚ] ℚ) :=
      ⟨fun a b => AlgEquiv.ext fun x => (a.commutes x).trans (b.commutes x).symm⟩
    sigmaAdelicAct ℚ ℚ (M4aHerbrand.identityDescent (𝓞 ℚ) ℚ ℚ) 1 = MonoidHom.id _ :=
  sigmaAdelicAct_one ℚ ℚ _

end Inhabitant

end AutomorphicForm

end
