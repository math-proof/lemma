import Structure.AutomorphicForm_CuspidalConstituent
import Def.NumberField_TateGlobalZeta

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate ENNReal InnerProductSpace


noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

variable (F : Type) [Field F] [NumberField F]

def detNormSlab (α β : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}


structure IsSlabFundamentalDomain (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : Prop where
  pos : 0 < α
  lt : α < β
  subset : Φ₀ ⊆ detNormSlab F α β
  isFundamentalDomain : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
    ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (detNormSlab F α β))


abbrev fdPins (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)


def weight (σ : ℝ) (x : AdelicGL2 (𝓞 F) F) : ℝ :=
  NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ)


def weightedMeasure (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (σ : ℝ) : Measure (AdelicGL2 (𝓞 F) F) :=
  ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀).withDensity fun x => ENNReal.ofReal (weight F σ x)


abbrev Carrier (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (σ : ℝ) : Type :=
  Lp ℂ 2 (weightedMeasure F Φ₀ σ)

theorem isAutomorphicFnAt_fdPins_iff (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsAutomorphicFnAt F (fdPins F Φ₀) ξ φ ↔
      IsLsXiFunction (𝓞 F) F ⊤ ξ φ ∧ MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
  lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ Φ₀ φ

def memberSubmodule (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | IsAutomorphicFnAt F (fdPins F Φ₀) ξ φ}
  zero_mem' := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ 0).mpr
    ⟨⟨fun _ _ => rfl, fun _ _ => by simp⟩, MemLp.zero⟩
  add_mem' := fun {a b} ha hb => by
    obtain ⟨⟨hal, hac⟩, ham⟩ := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ a).mp ha
    obtain ⟨⟨hbl, hbc⟩, hbm⟩ := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ b).mp hb
    exact (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ (a + b)).mpr
      ⟨⟨fun γ g => by rw [Pi.add_apply, Pi.add_apply, hal, hbl],
        fun z g => by rw [Pi.add_apply, Pi.add_apply, hac, hbc, mul_add]⟩, ham.add hbm⟩
  smul_mem' := fun c {a} ha => by
    obtain ⟨⟨hal, hac⟩, ham⟩ := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ a).mp ha
    exact (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ (c • a)).mpr
      ⟨⟨fun γ g => by rw [Pi.smul_apply, Pi.smul_apply, hal],
        fun z g => by rw [Pi.smul_apply, Pi.smul_apply, hac, smul_eq_mul, smul_eq_mul, mul_left_comm]⟩,
        ham.const_smul c⟩


def contMemberSubmodule (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | φ ∈ memberSubmodule F Φ₀ ξ ∧ Continuous φ}
  zero_mem' := ⟨(memberSubmodule F Φ₀ ξ).zero_mem, continuous_const⟩
  add_mem' := fun {a b} ha hb => ⟨(memberSubmodule F Φ₀ ξ).add_mem ha.1 hb.1, ha.2.add hb.2⟩
  smul_mem' := fun c {a} ha => ⟨(memberSubmodule F Φ₀ ξ).smul_mem c ha.1, ha.2.const_smul c⟩


theorem memLp_weightedMeasure_of_mem {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ memberSubmodule F Φ₀ ξ) :
    MemLp φ 2 (weightedMeasure F Φ₀ σ) := by
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  have hmem := ((isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ).mp hφ).2

  have hres : μ.restrict Φ₀ = (μ.restrict (detNormSlab F α β)).restrict Φ₀ := by
    rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet, Set.inter_eq_left.mpr hΦ₀.subset]
  have hae : ∀ᵐ x ∂(μ.restrict Φ₀), x ∈ Φ₀ := by
    rw [hres]; exact ae_restrict_mem₀ hΦ₀.isFundamentalDomain.nullMeasurableSet

  set C : ℝ := max (α ^ (-σ)) (β ^ (-σ)) with hC
  have hbound : ∀ x ∈ Φ₀, weight F σ x ≤ C := by
    intro x hx
    obtain ⟨h1, h2⟩ := hΦ₀.subset hx
    unfold weight
    rcases le_or_gt 0 (-σ) with hs | hs
    · exact (Real.rpow_le_rpow (hΦ₀.pos.le.trans h1) h2 hs).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hΦ₀.pos h1 hs.le).trans (le_max_left _ _)
  have hle : weightedMeasure F Φ₀ σ ≤ (ENNReal.ofReal C) • μ.restrict Φ₀ := by
    unfold weightedMeasure
    rw [← withDensity_const]
    exact withDensity_mono (hae.mono fun x hx => ENNReal.ofReal_le_ofReal (hbound x hx))
  exact (hmem.smul_measure ENNReal.ofReal_ne_top).mono_measure hle

def toCarrier {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : ↥(memberSubmodule F Φ₀ ξ) →ₗ[ℂ] Carrier F Φ₀ σ where
  toFun φ := (memLp_weightedMeasure_of_mem F hΦ₀ σ φ.2).toLp (φ : AdelicGL2 (𝓞 F) F → ℂ)
  map_add' φ ψ := MemLp.toLp_add (memLp_weightedMeasure_of_mem F hΦ₀ σ φ.2) (memLp_weightedMeasure_of_mem F hΦ₀ σ ψ.2)
  map_smul' c φ := MemLp.toLp_const_smul c (memLp_weightedMeasure_of_mem F hΦ₀ σ φ.2)


structure IsLift {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (Tfun : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) : Prop where
  mapsTo : ∀ φ, φ ∈ contMemberSubmodule F Φ₀ ξ → Tfun φ ∈ contMemberSubmodule F Φ₀ ξ
  comm : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (h : φ ∈ contMemberSubmodule F Φ₀ ξ),
    T (toCarrier F hΦ₀ σ ξ ⟨φ, h.1⟩) = toCarrier F hΦ₀ σ ξ ⟨Tfun φ, (mapsTo φ h).1⟩


end CuspidalSpectrum

end AutomorphicForm

end
