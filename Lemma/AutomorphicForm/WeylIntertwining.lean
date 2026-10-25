import Def.AutomorphicForm_AdelicLsXi
import Def.AutomorphicForm_ConstantTerm
import Def.AutomorphicForm_WeylIntertwining

noncomputable section

open Matrix MeasureTheory

namespace AutomorphicForm

section WeylElement

variable {K : Type*} [Field K]


@[simp] theorem gl2Weyl_val :
    ((gl2Weyl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

theorem gl2Weyl_inv : (gl2Weyl : GL (Fin 2) K)⁻¹ = gl2Weyl := Units.ext rfl

end WeylElement

section Intertwining

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [MeasurableSpace (NumberField.AdeleRing R K)]


theorem weylIntertwiningIntegral_const (ν : Measure (NumberField.AdeleRing R K))
    [IsProbabilityMeasure ν] (c : ℂ) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K ν (fun _ => c) g = c := by
  unfold weylIntertwiningIntegral
  simp [integral_const, measureReal_def]

theorem weylIntertwiningIntegral_zero_measure (f : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K 0 f g = 0 := by
  unfold weylIntertwiningIntegral
  simp

end Intertwining

end AutomorphicForm

end
