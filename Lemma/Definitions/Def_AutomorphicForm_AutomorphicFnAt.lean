import Lemma.Definitions.Def_AutomorphicForm_CarrierPins
import Lemma.Definitions.Def_AutomorphicForm_ConstantTerm

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

section LsXiAt

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def LsXiMemberAt [MeasurableSpace (AdelicGL2 R K)] (μ : Measure (AdelicGL2 R K))
    (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ) (D : Set (AdelicGL2 R K))
    (φ : AdelicGL2 R K → ℂ) : Prop :=
  @LsXiMember R K _ _ _ _ _ Z ξ ⟨μ⟩ D φ

theorem lsXiMemberAt_iff [MeasurableSpace (AdelicGL2 R K)] (μ : Measure (AdelicGL2 R K))
    (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ) (D : Set (AdelicGL2 R K))
    (φ : AdelicGL2 R K → ℂ) :
    LsXiMemberAt R K μ Z ξ D φ ↔ IsLsXiFunction R K Z ξ φ ∧ MemLp φ 2 (μ.restrict D) := by
  letI : MeasureSpace (AdelicGL2 R K) := ⟨μ⟩
  exact ⟨fun h => ⟨h.toIsLsXiFunction, h.memLp_two⟩, fun h => ⟨h.1, h.2⟩⟩

end LsXiAt

variable (F : Type) [Field F] [NumberField F]

def IsAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  @LsXiMemberAt (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z ξ pins.D φ

def IsCuspAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsAutomorphicFnAt F pins ξ φ ∧ @IsCuspidalFn _ pins.nS _ _ pins.ν unipotentGL2 φ

theorem isAutomorphicFnAt_zero (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsAutomorphicFnAt F pins ξ (fun _ => (0 : ℂ)) := by
  letI := pins.mS; letI : MeasureSpace (AdelicGL2 (𝓞 F) F) := ⟨pins.μ⟩
  exact lsXiMember_zero (𝓞 F) F pins.Z ξ pins.D

theorem isCuspAutomorphicFnAt_zero (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsCuspAutomorphicFnAt F pins ξ (fun _ => (0 : ℂ)) :=
  ⟨isAutomorphicFnAt_zero F pins ξ,
    fun g => by letI := pins.nS; exact constantTerm_zero pins.ν unipotentGL2 g⟩

theorem isAutomorphicFnAt_one_trivial (pins : CarrierPins F)
    (hDfin : @pins.μ pins.D < ⊤) :
    IsAutomorphicFnAt F pins (1 : pins.Z →* ℂˣ) (fun _ => (1 : ℂ)) := by
  letI := pins.mS; letI : MeasureSpace (AdelicGL2 (𝓞 F) F) := ⟨pins.μ⟩
  haveI : IsFiniteMeasure (pins.μ.restrict pins.D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hDfin⟩
  exact ⟨⟨fun _ _ => rfl, fun _ _ => by simp⟩, memLp_const 1⟩

theorem not_isCuspAutomorphicFnAt_one (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    [@IsProbabilityMeasure _ pins.nS pins.ν] :
    ¬ IsCuspAutomorphicFnAt F pins ξ (fun _ => (1 : ℂ)) := by
  intro ⟨_, hcusp⟩
  letI := pins.nS
  have h1 : (1 : ℂ) = 0 := by
    have := hcusp 1; rwa [constantTerm_const] at this
  exact one_ne_zero h1

end AutomorphicForm

end
