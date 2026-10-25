import Def.AutomorphicForm_UnipotentQuotient
import Abbrev.AutomorphicForm_RationalCentreUnipotentQuotient

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]


def rationalCentreUnipotentHaar : Measure (rationalCentreUnipotent K) :=
  Measure.sum fun a : Kˣ =>
    Measure.map
      (fun n : adelicUnipotent K =>
        (⟨globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
            * (n : AdelicGL2 (𝓞 K) K),
          Subgroup.mul_mem_sup ⟨a, rfl⟩ n.2⟩ : rationalCentreUnipotent K))
      (unipotentHaar K)

def rationalCentreUnipotentQuotientMeasure : Measure (RationalCentreUnipotentQuotient K) :=
  HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K)
    (rationalCentreUnipotentHaar K)

end AutomorphicForm

end
