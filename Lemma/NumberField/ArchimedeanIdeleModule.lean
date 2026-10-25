import Mathlib
import Lemma.GroupCohomology.RepPi
import Abbrev.NumberField_ArchimedeanIdeleModule
import Instance.NumberField_ArchimedeanIdeleModule

set_option autoImplicit false

open NumberField

namespace NumberField.InfPlaceDecomp

section general
variable {K : Type*} [Field K]

theorem uniformContinuous_congr_of_forall_eq (v : AbsoluteValue K ℝ) (f : K ≃+* K) (h : ∀ x, v (f x) = v x) :
    UniformContinuous (WithAbs.congr v v f) :=
  (AddMonoidHomClass.isometry_of_norm (WithAbs.congr v v f) fun x => by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
    exact h _).uniformContinuous

end general

variable (E K : Type*) [Field E] [Field K] [Algebra E K] (w : InfinitePlace K)


theorem apply_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) (x : K) : w (σ x) = w x := by
  rw [MulAction.mem_stabilizer_iff] at hσ
  conv_lhs => rw [← hσ]
  rw [InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]

theorem uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    UniformContinuous (WithAbs.congr w.1 w.1 (σ : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq w.1 (σ : K ≃+* K) (apply_of_mem σ hσ)

noncomputable def actRingEquiv (σ : decomp E K w) : w.Completion ≃+* w.Completion :=
  ((InfinitePlace.Completion.equiv w).trans
    (UniformSpace.Completion.mapRingEquiv (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2).continuous
      (by
        rw [WithAbs.congr_symm]
        exact (uniformContinuous_congr_of_mem ((σ⁻¹ : decomp E K w) : K ≃ₐ[E] K) (σ⁻¹).2).continuous))).trans
    (InfinitePlace.Completion.equiv w).symm

theorem actRingEquiv_apply (σ : decomp E K w) (x : w.Completion) :
    (actRingEquiv σ x).toCompletion =
      UniformSpace.Completion.map (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion :=
  rfl

theorem actRingEquiv_coe (σ : decomp E K w) (x : WithAbs w.1) :
    actRingEquiv σ (x : w.Completion) = ((WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K) x : WithAbs w.1) : w.Completion) := by
  apply InfinitePlace.Completion.ext
  rw [actRingEquiv_apply, InfinitePlace.Completion.coe_toCompletion,
    InfinitePlace.Completion.coe_toCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]

theorem continuous_actRingEquiv (σ : decomp E K w) : Continuous (actRingEquiv σ) := by
  have : (actRingEquiv σ : w.Completion → w.Completion) =
      InfinitePlace.Completion.ofCompletion ∘
        UniformSpace.Completion.map (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) ∘
        InfinitePlace.Completion.toCompletion :=
    funext fun x => InfinitePlace.Completion.ext (h := actRingEquiv_apply σ x)
  rw [this]
  exact (InfinitePlace.Completion.continuous_ofCompletion w).comp
    (UniformSpace.Completion.continuous_map.comp (InfinitePlace.Completion.continuous_toCompletion w))

theorem actRingEquiv_one : actRingEquiv (1 : decomp E K w) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  apply InfinitePlace.Completion.ext
  rw [actRingEquiv_apply]
  change _ = id x.toCompletion
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map continuous_id
    fun a => ?_) _
  rw [UniformSpace.Completion.map_coe
    (uniformContinuous_congr_of_mem ((1 : decomp E K w) : K ≃ₐ[E] K) (1 : decomp E K w).2)]
  rfl

theorem actRingEquiv_mul (σ τ : decomp E K w) : actRingEquiv (σ * τ) = (actRingEquiv τ).trans (actRingEquiv σ) := by
  apply RingEquiv.ext
  intro x
  apply InfinitePlace.Completion.ext
  change (actRingEquiv (σ * τ) x).toCompletion = (actRingEquiv σ (actRingEquiv τ x)).toCompletion
  rw [actRingEquiv_apply, actRingEquiv_apply, actRingEquiv_apply]
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map
    (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map) fun a => ?_) _
  change _ = UniformSpace.Completion.map _ (UniformSpace.Completion.map _ _)
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem ((σ * τ : decomp E K w) : K ≃ₐ[E] K) (σ * τ).2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (τ : K ≃ₐ[E] K) τ.2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]
  rfl

noncomputable def actHom : decomp E K w →* (w.Completion ≃+* w.Completion) where
  toFun := actRingEquiv
  map_one' := actRingEquiv_one
  map_mul' σ τ := actRingEquiv_mul σ τ

theorem smul_withAbs_def (σ : decomp E K w) (y : WithAbs w.1) : σ • y = WithAbs.toAbs w.1 ((σ : K ≃ₐ[E] K) y.ofAbs) := rfl

theorem smul_def (σ : decomp E K w) (x : w.Completion) : σ • x = actRingEquiv σ x := rfl

theorem coe_smul_units (σ : decomp E K w) (u : (w.Completion)ˣ) : ((σ • u : (w.Completion)ˣ) : w.Completion) = σ • (u : w.Completion) := rfl

variable (E K w) in


end NumberField.InfPlaceDecomp

namespace NumberField.ArchIdele

open scoped NumberField.InfPlaceDecomp

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem exists_above (v : InfinitePlace E) : ∃ w : InfinitePlace K, w.comap (algebraMap E K) = v :=
  InfinitePlace.comap_surjective v

noncomputable def above (v : InfinitePlace E) : InfinitePlace K := (exists_above E K v).choose

theorem comap_above (v : InfinitePlace E) : (above E K v).comap (algebraMap E K) = v := (exists_above E K v).choose_spec

noncomputable abbrev fibre (v : InfinitePlace E) : Rep ℤ (K ≃ₐ[E] K) :=
  Rep.coind (InfPlaceDecomp.decomp E K (above E K v)).subtype (InfPlaceDecomp.localUnits E K (above E K v))


end NumberField.ArchIdele
