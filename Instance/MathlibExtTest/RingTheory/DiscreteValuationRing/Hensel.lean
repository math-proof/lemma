/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/Hensel.lean -/


module

public import Theorem.RingTheory.DiscreteValuationRing.Hensel
public import Theorem.Int.DiscreteValuationRing.Hensel
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Tactic.NormNum
public import Theorem.MathlibExtTest.RingTheory.DiscreteValuationRing.Hensel
@[expose] public section

noncomputable section

open Polynomial IsLocalRing Ring

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

end
