import Def.AutomorphicForm_ArchWeightChar

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open scoped Classical

namespace AutomorphicForm

section Furniture

variable {K L : Type*} [NormedField K] [NormedField L]

noncomputable def glEquivOfRingEquiv (e : K ≃+* L) : GL (Fin 2) K ≃* GL (Fin 2) L :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) e).toMulEquiv

noncomputable def rowIsometrySubgroup₀Map (e : K ≃+* L)
    (he : ∀ x : K, ‖e x‖ = ‖x‖) :
    rowIsometrySubgroup₀ K →* rowIsometrySubgroup₀ L where
  toFun k := ⟨glEquivOfRingEquiv e k, map_mem_rowIsometrySubgroup₀_of_normPreserving e he k k.2⟩
  map_one' := by ext; simp [glEquivOfRingEquiv]
  map_mul' k k' := by ext; simp [glEquivOfRingEquiv]

end Furniture

section RealPlace

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

noncomputable def archWeightOneAt {w : InfinitePlace F} (hw : w.IsReal) :
    rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  archWeightOneℝ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
    (norm_ringEquivRealOfIsReal hw))

noncomputable def archWeightCharAt {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ) :
    rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  (zpowGroupHom n).comp (archWeightOneAt hw)

omit [NumberField F] in

end RealPlace

section Family

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in

noncomputable def archWeightCharFamily (n : ℤ) :
    ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  fun w => if hw : w.IsReal then archWeightCharAt hw n else 1

omit [NumberField F] in
end Family

end AutomorphicForm
