import Lemma.AutomorphicForm.IsotypicCuspSpace
import Lemma.AutomorphicForm.FactorizableTestFn
import Structure.AutomorphicForm_CuspidalConstituent

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

namespace CuspidalConstituent

variable (F : Type) [Field F] [NumberField F]


theorem rightTranslate_apply (g x : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F g φ x = φ (x * g) := rfl

def rightRegular : Representation ℂ (AdelicGL2 (𝓞 F) F) (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun g :=
    { toFun := rightTranslate F g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext φ x; simp [rightTranslate]
  map_mul' g h := by ext φ x; simp [rightTranslate, mul_assoc]

@[simp] theorem rightRegular_apply (g : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightRegular F g φ = rightTranslate F g φ := rfl

theorem rightTranslate_rightTranslate (g g' : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F g' (rightTranslate F g φ) = rightTranslate F (g' * g) φ := by
  funext x; simp [rightTranslate, mul_assoc]

theorem rightTranslate_add (g : AdelicGL2 (𝓞 F) F) (φ ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F g (φ + ψ) = rightTranslate F g φ + rightTranslate F g ψ := rfl

theorem rightTranslate_smul (g : AdelicGL2 (𝓞 F) F) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F g (c • φ) = c • rightTranslate F g φ := rfl

theorem rightTranslate_zero (g : AdelicGL2 (𝓞 F) F) : rightTranslate F g (0 : AdelicGL2 (𝓞 F) F → ℂ) = 0 := rfl

theorem continuous_rightTranslate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Continuous (rightTranslate F g φ) :=
  hφ.comp (continuous_mul_const g)

theorem forall_isSmoothCuspAutomorphicFnAt_rightTranslate_rightTranslate {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : ∀ g : AdelicGL2 (𝓞 F) F, IsSmoothCuspAutomorphicFnAt F pins ξ (rightTranslate F g φ)) (g : AdelicGL2 (𝓞 F) F) :
    ∀ g' : AdelicGL2 (𝓞 F) F, IsSmoothCuspAutomorphicFnAt F pins ξ (rightTranslate F g' (rightTranslate F g φ)) := by
  intro g'; rw [rightTranslate_rightTranslate]; exact h _

theorem rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule (tys : ArchTypeFamily F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archCutSubmodule F tys) (v : InfinitePlace F)
    (k : rowIsometrySubgroup₀ v.Completion) :
    rightTranslate F (rowIsometryInclAt₀ F v k) φ ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  have key : ∀ i : Fin (tys.card w),
      (archTypeSubmoduleAt F w (tys.rep w i)).map (rightRegular F (rowIsometryInclAt₀ F v k))
        ≤ archTypeSubmoduleAt F w (tys.rep w i) := by
    intro i f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
    by_cases hvw : v = w
    · subst hvw
      exact comp_mul_mem_typeSubmodule hf₀ k
    · refine comp_mul_mem_typeSubmodule_of_commute hf₀ _ fun k' => ?_
      rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply]
      exact commute_adelicArchGLInclAt_of_ne F hvw _ _
  have hmap : (⨆ i, archTypeSubmoduleAt F w (tys.rep w i)).map (rightRegular F (rowIsometryInclAt₀ F v k))
      ≤ ⨆ i, archTypeSubmoduleAt F w (tys.rep w i) := by
    rw [Submodule.map_iSup]; exact iSup_mono key
  exact hmap (Submodule.mem_map_of_mem (hφ w))


theorem rightTranslate_rowIsometryInclAt₀_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) (v : InfinitePlace F)
    (k : rowIsometrySubgroup₀ v.Completion) :
    rightTranslate F (rowIsometryInclAt₀ F v k) φ ∈ cuspKFiniteSubmodule F pins ξ := by
  refine Submodule.span_induction
    (p := fun φ _ => rightTranslate F (rowIsometryInclAt₀ F v k) φ ∈ cuspKFiniteSubmodule F pins ξ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, tys, htys⟩
    exact Submodule.subset_span ⟨forall_isSmoothCuspAutomorphicFnAt_rightTranslate_rightTranslate F hsat _,
      continuous_rightTranslate F hcont _, tys, rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule F tys htys v k⟩
  · show rightTranslate F _ 0 ∈ _
    rw [rightTranslate_zero]; exact (cuspKFiniteSubmodule F pins ξ).zero_mem
  · intro u w _ _ hu hw
    show rightTranslate F _ (u + w) ∈ _
    rw [rightTranslate_add]; exact (cuspKFiniteSubmodule F pins ξ).add_mem hu hw
  · intro c u _ hu
    show rightTranslate F _ (c • u) ∈ _
    rw [rightTranslate_smul]; exact (cuspKFiniteSubmodule F pins ξ).smul_mem c hu


def IsCuspConstituent (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Prop :=
  IsCuspSubrep F pins ξ V ∧ V ≠ ⊥ ∧
    ∀ W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), IsCuspSubrep F pins ξ W → W ≤ V → W = ⊥ ∨ W = V

def CuspConstituentMeets (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Prop :=
  ∃ φ ∈ V, φ ≠ 0 ∧ IsIsotypicCuspFormAt F pins ξ N S Ψ φ

def cuspConstituentIsotypicCut (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  V ⊓ isotypicCuspSubmodule F pins ξ N S Ψ

def levelInvariantSubmodule (pins : CarrierPins F) (N : Ideal (𝓞 F)) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ pins.U N, φ (g * u) = φ g}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun {a b} ha hb g u hu => by simp only [Pi.add_apply, ha g u hu, hb g u hu]
  smul_mem' := fun c {a} ha g u hu => by simp only [Pi.smul_apply, ha g u hu]

theorem isCuspSubrep_bot (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsCuspSubrep F pins ξ ⊥ :=
  ⟨bot_le, fun g _ φ hφ => by rw [(Submodule.mem_bot ℂ).mp hφ]; exact Submodule.zero_mem _,
    fun w k φ hφ => by rw [(Submodule.mem_bot ℂ).mp hφ]; exact Submodule.zero_mem _,
    fun f _ _ _ φ hφ => by
      rw [(Submodule.mem_bot ℂ).mp hφ]
      exact (Submodule.mem_bot ℂ).mpr (rightConv_zero_left F f)⟩

theorem not_isCuspConstituent_bot (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    ¬ IsCuspConstituent F pins ξ ⊥ := fun h => h.2.1 rfl

theorem inf_isotypicCuspSubmodule_ne_bot_of_cuspConstituentMeets {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Ψ : HeckeEigensystem F ℂ}
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (h : CuspConstituentMeets F pins ξ N S Ψ V) :
    V ⊓ isotypicCuspSubmodule F pins ξ N S Ψ ≠ ⊥ := by
  obtain ⟨φ, hφV, hφ0, hφ⟩ := h
  intro hbot
  have : φ ∈ V ⊓ isotypicCuspSubmodule F pins ξ N S Ψ := ⟨hφV, hφ.mem_isotypicCuspSubmodule⟩
  rw [hbot, Submodule.mem_bot] at this
  exact hφ0 this

end CuspidalConstituent

end AutomorphicForm

end
