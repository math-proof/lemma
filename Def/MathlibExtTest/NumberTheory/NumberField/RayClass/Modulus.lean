/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/Modulus.lean -/

import Theorem.NumberTheory.NumberField.RayClass.Modulus.Part5
import Lemma.Nat.NumberField.RayClass.Modulus
@[expose] public noncomputable section

open scoped Classical nonZeroDivisors
open NumberField


namespace N403ModulusTest

variable {K : Type*} [Field K] [NumberField K]

def qPlace : RealPlace ℚ := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

end N403ModulusTest
