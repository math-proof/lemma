import Lemma.Definitions.Def_AutomorphicForm_UnipotentQuotient

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]

abbrev rationalCentre : Subgroup (AdelicGL2 (𝓞 K) K) :=
  ((globalPoints (𝓞 K) K).comp
    (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom)).range

abbrev rationalCentreUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalCentre K ⊔ adelicUnipotent K

abbrev RationalCentreUnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (rationalCentreUnipotent K) (AdelicGL2 (𝓞 K) K)

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
