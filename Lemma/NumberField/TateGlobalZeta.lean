import Def.NumberField_AdelicFourier
import Def.NumberField_AdelicVolume
import Def.NumberField_TateGlobalZeta

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.AdelicVolume
open AutomorphicForm IsDedekindDomain
open scoped NNReal

noncomputable section

namespace NumberField.TateGlobal

variable (F : Type) [Field F] [NumberField F]


variable {F}

theorem ideleNorm_pos (x : (AdeleRing (𝓞 F) F)ˣ) : 0 < ideleNorm F x :=
  NNReal.coe_pos.mpr (distribHaarChar_pos)


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
