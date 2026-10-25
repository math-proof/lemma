/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/Group.lean -/

import Def.NumberTheory.NumberField.RayClass.Group
import Lemma.Nat.NumberField.RayClass.Group
@[expose] public noncomputable section

open scoped Classical nonZeroDivisors
open NumberField


namespace N404RayClassGroupTest

variable {K : Type*} [Field K] [NumberField K]

example (m : Modulus K) : CommGroup (Modulus.RayClassGroup m) :=
  inferInstance

example (m : Modulus K) :
    Function.Surjective (Modulus.rayClassMap (K := K) m) :=
  Modulus.rayClassMap_surjective m

example (m : Modulus K) : Modulus.rayClassMap m 1 = 1 := map_one _

example (m : Modulus K) (x : Modulus.coprimeFractionalIdeals m)
    (h : x ∈ Modulus.rayGroup m) : Modulus.rayClassMap m x = 1 := by
  rw [Modulus.rayClassMap_eq_one_iff]
  exact h

example (m : Modulus K) (a b : Modulus.coprimeFractionalIdeals m) :
    Modulus.rayClassMap m a = Modulus.rayClassMap m b ↔
      a / b ∈ Modulus.rayGroup m :=
  Modulus.rayClassMap_eq_rayClassMap_iff m a b

end N404RayClassGroupTest
