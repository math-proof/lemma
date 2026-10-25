import Def.AutomorphicForm_SmoothAutomorphicFnAt
import Def.AutomorphicForm_HeckeEigensystemMap
import Structure.LocalLanglands_HeckeCosetSystem

open IsDedekindDomain NumberField MeasureTheory Matrix
open AutomorphicForm HeckeIntegralSeam

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

namespace SmoothCusp

def heckeCosetSum {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ∑ i, φ (g * reps i)


def IsHeckeCosetEigenfunctionAt (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (gv : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) : Prop :=
  ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
    IsHeckeCosetSystem U gv reps ∧
    ∀ g : AdelicGL2 (𝓞 F) F, heckeCosetSum F reps φ g = c * φ g

end SmoothCusp

open SmoothCusp

structure SmoothCuspRealizationAt (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) where
  toFun : AdelicGL2 (𝓞 F) F → ℂ
  exists_ne_zero : ∃ g : AdelicGL2 (𝓞 F) F, toFun g ≠ 0
  centralChar : pins.Z →* ℂˣ
  smoothCusp : IsSmoothCuspAutomorphicFnAt F pins centralChar toFun
  level_invariant : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ pins.U Φ.level, toFun (g * u) = toFun g
  exceptionalSet : Finset (HeightOneSpectrum (𝓞 F))
  hecke_eigen : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ exceptionalSet →
    IsHeckeCosetEigenfunctionAt F (pins.U Φ.level) (pins.gen v) v toFun (Φ.a v)
  central_eigen : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ exceptionalSet →
    ∀ g : AdelicGL2 (𝓞 F) F,
      toFun (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (pins.gen v)) * g)
        = Φ.b v * toFun g


variable {F}


variable (F)

namespace SmoothCusp


end SmoothCusp

variable {F}


section Inhabitor

variable (F)


end Inhabitor

end AutomorphicForm

end
