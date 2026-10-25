import Def.MeasureTheory_ScalingDichotomy
import Lemma.Matrix.WindowedSiegelTopology
import Instance.NumberField_AdelicCentre

open MeasureTheory Set IsDedekindDomain NumberField MeasureTheory.ScalingDichotomy
open scoped ENNReal

noncomputable section

namespace NumberField.AdelicVolume

section Adelic

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in

def archCentralUnit (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (Function.update (1 : InfiniteAdeleRing F) v₀ (a : v₀.Completion), 1)
  inv := (Function.update (1 : InfiniteAdeleRing F) v₀ ((a⁻¹ : (v₀.Completion)ˣ) : v₀.Completion), 1)
  val_inv := by
    sorry
  inv_val := by
    sorry

variable {F}


def archDetNorm (v₀ : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  ‖((archComponent F v₀ (glArch (𝓞 F) F g) : GL (Fin 2) v₀.Completion) :
      Matrix (Fin 2) (Fin 2) v₀.Completion).det‖


end Adelic

end NumberField.AdelicVolume

end
