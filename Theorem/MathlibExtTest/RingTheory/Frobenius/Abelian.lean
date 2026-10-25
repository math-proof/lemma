/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Frobenius/Abelian.lean -/


import Theorem.RingTheory.Frobenius.Abelian
import Lemma.Int.Frobenius.Abelian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Finite G] [Algebra.IsInvariant R S G]

/-!
# Regression examples for the abelian Frobenius independence API

These examples exercise the root-level declaration
`arithFrobAt_eq_of_under_eq` through the public import surface, as a
downstream user would see it:

* a generic `IsMulCommutative G` consumer;
* a number-field consumer with `G = (L ≃ₐ[K] L)` showing that
  `[IsAbelianGalois K L]` supplies the needed commutativity instance.
-/


-- Generic consumer: commutativity collapses the Frobenius conjugacy class.
example [IsMulCommutative G] (Q Q' : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Q'.IsPrime] [Finite (S ⧸ Q')]
    (h : Q.under R = Q'.under R) :
    arithFrobAt R G Q = arithFrobAt R G Q' :=
  arithFrobAt_eq_of_under_eq Q Q' h

section NumberField

variable (K L : Type*) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

-- `IsAbelianGalois K L` supplies commutativity of the Galois group.
example : IsMulCommutative (L ≃ₐ[K] L) := inferInstance

-- Number-field consumer: Frobenius elements above the same base prime agree.
-- The Galois action/invariance instances below are test-local hypotheses:
-- Mathlib synthesizes the `MulSemiringAction`, `Finite`, and `Algebra`
-- instances, but not `SMulCommClass` / `Algebra.IsInvariant` for
-- `RingOfIntegers`.
example (Q Q' : Ideal (NumberField.RingOfIntegers L))
    [Q.IsPrime] [Finite (NumberField.RingOfIntegers L ⧸ Q)]
    [Q'.IsPrime] [Finite (NumberField.RingOfIntegers L ⧸ Q')]
    [SMulCommClass (L ≃ₐ[K] L)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)]
    [Algebra.IsInvariant (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) (L ≃ₐ[K] L)]
    (h : Q.under (NumberField.RingOfIntegers K) =
      Q'.under (NumberField.RingOfIntegers K)) :
    arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q =
      arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q' :=
  arithFrobAt_eq_of_under_eq Q Q' h

end NumberField
