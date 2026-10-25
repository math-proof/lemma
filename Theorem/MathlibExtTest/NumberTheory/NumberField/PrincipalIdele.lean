/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/PrincipalIdele.lean -/

/-
Author: @toskua, Avocado
-/

import Theorem.NumberTheory.NumberField.PrincipalIdele
import Lemma.Nat.NumberField.PrincipalIdele


noncomputable section

open NumberField NumberField.TopologicalIdeleGroup

variable (K : Type*) [Field K] [NumberField K]

example : DiscreteTopology (principalIdeles (𝓞 K) K) :=
  principalIdeles_discrete K

example : IsOpen ({1} : Set (principalIdeles (𝓞 ℚ) ℚ)) := by
  let _ : DiscreteTopology (principalIdeles (𝓞 ℚ) ℚ) :=
    principalIdeles_discrete ℚ
  exact isOpen_discrete _

example (X : Type*) [TopologicalSpace X] (f : principalIdeles (𝓞 K) K → X) :
    Continuous f := by
  let _ : DiscreteTopology (principalIdeles (𝓞 K) K) :=
    principalIdeles_discrete K
  exact continuous_of_discreteTopology

end
