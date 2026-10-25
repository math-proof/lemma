/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean -/

/-
Author: @toskua, Avocado
-/


import Theorem.RingTheory.Polynomial.Eisenstein.AdjoinRoot
import Lemma.Int.Polynomial.Eisenstein.AdjoinRoot
import Mathlib.NumberTheory.Padics.PadicIntegers
import Theorem.MathlibExtTest.RingTheory.Polynomial.Eisenstein.AdjoinRoot
open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable (f : A[X]) (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic) (hdeg : 0 < f.natDegree)


namespace ConcretePadicEisenstein

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

end ConcretePadicEisenstein
