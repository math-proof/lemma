import Def.AutomorphicForm_SmoothAutomorphicFnAt
import Def.AutomorphicForm_ArchDerivCasimir
import Def.LanglandsTunnell_DeltaLift

open MeasureTheory NumberField AutomorphicForm

noncomputable section

namespace RSCarrier

def archMeasure : @Measure (GL (Fin 2) ℝ) (borel (GL (Fin 2) ℝ)) :=
  letI := borel (GL (Fin 2) ℝ)
  (Measure.comap (fun g : GL (Fin 2) ℝ => fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)
      (volume : Measure (Fin 2 → Fin 2 → ℝ))).withDensity
    fun g => ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det g : ℝ)| ^ 2)⁻¹

def finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) : finiteAdelicGL2Subgroup ℚ :=
  ⟨(archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (LanglandsTunnell.ratArchGL2 g))⁻¹ * g, by
    rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_inv, inv_mul_eq_one]
    rw [show AdelicLevel.glArch (𝓞 ℚ) ℚ
        (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (LanglandsTunnell.ratArchGL2 g)) =
        archGLIncl ℚ default (glEquivOfRingEquiv
          (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm
          (LanglandsTunnell.ratArchGL2 g)) from glArch_adelicArchGLIncl ℚ _]
    refine Units.ext (Matrix.ext fun i j => funext fun v => ?_)
    obtain rfl : v = default := Subsingleton.elim v default
    refine (congrArg (fun u : GL (Fin 2) (default : InfinitePlace ℚ).Completion =>
        (u : Matrix (Fin 2) (Fin 2) (default : InfinitePlace ℚ).Completion) i j)
      (archComponent_archGLIncl_self ℚ default _)).trans ?_
    rw [glEquivOfRingEquiv_apply_entry]
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal _).symm_apply_apply _⟩

end RSCarrier

end
