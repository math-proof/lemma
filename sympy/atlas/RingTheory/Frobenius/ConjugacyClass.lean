/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/ConjugacyClass.lean -/

import Mathlib.Algebra.Group.Conj
import Mathlib.RingTheory.Frobenius

/-!
# Conjugacy class of the arithmetic Frobenius at an unramified prime

Let `S` be a commutative `R`-algebra with a semilinear action of a finite group `G`
fixing `R` pointwise (`Algebra.IsInvariant R S G`), and let `Q` be a prime of `S`
with finite residue field at which `S` is unramified over `R`. Mathlib provides an
arbitrary choice of Frobenius element `arithFrobAt R G Q : G` at `Q`, well defined
up to conjugacy over each prime of `R` (`isConj_arithFrobAt`).

This module packages that choice as a conjugacy class:

* `arithFrobConjClass`: the conjugacy class of `arithFrobAt R G Q`.
* `arithFrobConjClass_mem_carrier`: the chosen Frobenius lies in the class.
* `arithFrobConjClass_eq_of_under_eq`: primes lying over the same prime of `R`
  give the same class.

These declarations live in the root namespace, matching `arithFrobAt` and
`isConj_arithFrobAt`.
-/

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Finite G] [Algebra.IsInvariant R S G]

/-- The conjugacy class of the arithmetic Frobenius element `arithFrobAt R G Q`
at an unramified prime `Q` with finite residue field. -/
noncomputable def arithFrobConjClass (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Algebra.IsUnramifiedAt R Q] : ConjClasses G :=
  ConjClasses.mk (arithFrobAt R G Q)

/-- The chosen Frobenius element lies in its conjugacy class. -/
theorem arithFrobConjClass_mem_carrier (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Algebra.IsUnramifiedAt R Q] :
    arithFrobAt R G Q ∈ (arithFrobConjClass (R := R) (G := G) Q).carrier :=
  ConjClasses.mem_carrier_mk

/-- Primes of `S` lying over the same prime of `R` give the same Frobenius
conjugacy class. -/
theorem arithFrobConjClass_eq_of_under_eq (Q Q' : Ideal S) [Q.IsPrime]
    [Finite (S ⧸ Q)] [Algebra.IsUnramifiedAt R Q] [Q'.IsPrime]
    [Finite (S ⧸ Q')] [Algebra.IsUnramifiedAt R Q']
    (h : Q.under R = Q'.under R) :
    arithFrobConjClass (R := R) (G := G) Q =
      arithFrobConjClass (R := R) (G := G) Q' := by
  unfold arithFrobConjClass
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_arithFrobAt R G Q Q' h
