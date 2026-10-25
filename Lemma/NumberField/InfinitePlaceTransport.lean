import Mathlib

set_option autoImplicit false

open NumberField

namespace NumberField.InfinitePlaceTransport

section general
variable {R S : Type*} [Field R] [Field S]

theorem uniformContinuous_congr_of_forall_eq (v : AbsoluteValue R ℝ) (v' : AbsoluteValue S ℝ) (f : R ≃+* S)
    (h : ∀ x, v' (f x) = v x) : UniformContinuous (WithAbs.congr v v' f) :=
  (AddMonoidHomClass.isometry_of_norm (WithAbs.congr v v' f) fun x => by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
    exact h _).uniformContinuous

end general

variable {E K : Type*} [Field E] [Field K] [Algebra E K]

theorem apply_apply_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w') (x : K) : w' (σ x) = w x := by
  rw [← h, InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]

theorem inv_smul_eq_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w') : σ⁻¹ • w' = w := by
  rw [← h, inv_smul_smul]

theorem uniformContinuous_congr_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w') :
    UniformContinuous (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq w.1 w'.1 _ (apply_apply_of_smul_eq h)

noncomputable def transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') : w.Completion ≃+* w'.Completion :=
  (InfinitePlace.Completion.equiv w).trans
    ((UniformSpace.Completion.mapRingEquiv (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_smul_eq h).continuous
      ((uniformContinuous_congr_of_smul_eq (inv_smul_eq_of_smul_eq h)).continuous.congr fun _ => rfl)).trans
    (InfinitePlace.Completion.equiv w').symm)

theorem transport_apply (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : w.Completion) :
    transport σ h x = .ofCompletion
      (UniformSpace.Completion.map (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion) :=
  rfl

theorem toCompletion_transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : w.Completion) :
    (transport σ h x).toCompletion
      = UniformSpace.Completion.map (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion :=
  rfl

theorem transport_coe (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : WithAbs w.1) :
    transport σ h (x : w.Completion) = ((WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K) x : WithAbs w'.1) : w'.Completion) := by
  rw [transport_apply, InfinitePlace.Completion.coe_toCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_smul_eq h)]

theorem continuous_transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') : Continuous (transport σ h) :=
  (InfinitePlace.Completion.continuous_ofCompletion w').comp
    (UniformSpace.Completion.continuous_map.comp (InfinitePlace.Completion.continuous_toCompletion w))

noncomputable abbrev transportUnits (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') :
    (w.Completion)ˣ ≃* (w'.Completion)ˣ :=
  Units.mapEquiv (transport σ h).toMulEquiv

theorem coe_transportUnits (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (u : (w.Completion)ˣ) :
    ((transportUnits σ h u : (w'.Completion)ˣ) : w'.Completion) = transport σ h (u : w.Completion) := rfl

end NumberField.InfinitePlaceTransport
