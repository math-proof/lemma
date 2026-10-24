import Lemma.Definitions.Def_NumberField_AdelicFourier
import Lemma.Definitions.Def_NumberField_AdelicVolume

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.AdelicVolume
open AutomorphicForm IsDedekindDomain
open scoped NNReal

noncomputable section

namespace NumberField.TateGlobal

variable (F : Type) [Field F] [NumberField F]

def normOneIdeles : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (distribHaarChar (AdeleRing (𝓞 F) F)).ker

def ideleNorm (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  ((distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ≥0) : ℝ)

variable {F}

theorem ideleNorm_pos (x : (AdeleRing (𝓞 F) F)ˣ) : 0 < ideleNorm F x :=
  NNReal.coe_pos.mpr (distribHaarChar_pos)

def zetaIntegral {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ} (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (f : AdeleRing (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν

def localChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* ℂˣ :=
  χ.comp ((Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v))

def archUnitHom (w : InfinitePlace F) : (w.Completion)ˣ →* (AdeleRing (𝓞 F) F)ˣ where
  toFun := archCentralUnit F w
  map_one' := by
    classical
    refine Units.ext (Prod.ext (funext fun v => ?_) rfl)
    show Function.update (1 : InfiniteAdeleRing F) w ((1 : InfiniteAdeleRing F) w) v
      = (1 : InfiniteAdeleRing F) v
    rw [Function.update_eq_self]
  map_mul' a b := by
    classical
    refine Units.ext (Prod.ext (funext fun v => ?_) (one_mul 1).symm)
    show Function.update (1 : InfiniteAdeleRing F) w (((a * b : (w.Completion)ˣ)) : w.Completion) v
      = Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion) v
          * Function.update (1 : InfiniteAdeleRing F) w (b : w.Completion) v
    by_cases hv : v = w
    · subst hv
      simp [Function.update_self]
    · rw [Function.update_of_ne hv, Function.update_of_ne hv, Function.update_of_ne hv]
      exact (mul_one _).symm

def archLocalChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) :
    (w.Completion)ˣ →* ℂˣ :=
  χ.comp (archUnitHom w)

def IsUnramifiedCharAt (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ t : (v.adicCompletion F)ˣ, (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      localChar χ v t = 1

def integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (AdeleRing (𝓞 F) F) :=
  {x | ∀ v ∉ S, (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}

def IsFactorizableStandardOutside (f : AdeleRing (𝓞 F) F → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : (w : InfinitePlace F) → w.Completion → ℂ)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) : Prop :=
  ∀ x, f x = (integralOutside S).indicator
      (fun x => (∏ w, g w (x.1 w)) * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x

theorem ideleNorm_mul (x y : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F (x * y) = ideleNorm F x * ideleNorm F y := by
  simp [ideleNorm, map_mul]

theorem mem_normOneIdeles_iff (x : (AdeleRing (𝓞 F) F)ˣ) : x ∈ normOneIdeles F ↔ ideleNorm F x = 1 := by
  simp [normOneIdeles, ideleNorm, MonoidHom.mem_ker]

theorem localChar_apply (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F))
    (t : (v.adicCompletion F)ˣ) :
    localChar χ v t = χ (Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t)) := rfl

theorem archUnitHom_apply (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    archUnitHom w a = archCentralUnit F w a := rfl

theorem archLocalChar_apply (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    archLocalChar χ w a = χ (archCentralUnit F w a) := rfl

end NumberField.TateGlobal

end
