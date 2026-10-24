import Lemma.Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Lemma.Definitions.Def_NumberField_AdelicLevel

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]

abbrev rationalDiagOne : Subgroup (AdelicGL2 (𝓞 K) K) :=
  ((globalPoints (𝓞 K) K).comp (diagOne (A := K))).range

abbrev rationalTorus : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalCentre K ⊔ rationalDiagOne K

abbrev rationalTorusUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalTorus K ⊔ adelicUnipotent K

abbrev RationalTorusUnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (rationalTorusUnipotent K) (AdelicGL2 (𝓞 K) K)

def rationalTorusUnipotentHaar : Measure (rationalTorusUnipotent K) :=
  Measure.sum fun za : Kˣ × Kˣ =>
    Measure.map
      (fun n : adelicUnipotent K =>
        (⟨globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom za.1)
            * globalPoints (𝓞 K) K (diagOne za.2) * (n : AdelicGL2 (𝓞 K) K),
          Subgroup.mul_mem_sup
            (Subgroup.mul_mem_sup ⟨za.1, rfl⟩ ⟨za.2, rfl⟩) n.2⟩ : rationalTorusUnipotent K))
      (unipotentHaar K)

def rationalTorusUnipotentQuotientMeasure : Measure (RationalTorusUnipotentQuotient K) :=
  HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K)
    (rationalTorusUnipotentHaar K)

end AutomorphicForm

end
