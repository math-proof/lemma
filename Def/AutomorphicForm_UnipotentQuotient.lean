import Def.AutomorphicForm_ConstantTerm
import Def.AutomorphicForm_AdelicLsXi
import Instance.NumberField_AdelicHaar
import Def.NumberField_AdelicBox
import Def.HaarQuotient
import Abbrev.AutomorphicForm_UnipotentQuotient

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]

def toAdelicUnipotent (x : AdeleRing (𝓞 K) K) : adelicUnipotent K :=
  (unipotentGL2Hom (R := AdeleRing (𝓞 K) K)).rangeRestrict (Multiplicative.ofAdd x)

def unipotentHaar : Measure (adelicUnipotent K) :=
  Measure.map (toAdelicUnipotent K)
    (((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K)

def unipotentQuotientMeasure : Measure (UnipotentQuotient K) :=
  HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (adelicUnipotent K) (unipotentHaar K)

end AutomorphicForm

end
