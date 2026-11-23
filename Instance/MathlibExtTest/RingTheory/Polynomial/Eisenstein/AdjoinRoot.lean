/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean -/

/-
Author: @toskua, Avocado
-/


module

public import Theorem.RingTheory.Polynomial.Eisenstein.AdjoinRoot
public import Theorem.Int.Polynomial.Eisenstein.AdjoinRoot
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Theorem.MathlibExtTest.RingTheory.Polynomial.Eisenstein.AdjoinRoot
@[expose] public section

open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable (f : A[X]) (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic) (hdeg : 0 < f.natDegree)


namespace ConcretePadicEisenstein

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

end ConcretePadicEisenstein
