/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/Hensel.lean -/


import Theorem.RingTheory.DiscreteValuationRing.Hensel
import Lemma.Int.DiscreteValuationRing.Hensel
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.NormNum
import Theorem.MathlibExtTest.RingTheory.DiscreteValuationRing.Hensel


noncomputable section

open Polynomial IsLocalRing Ring

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

end
