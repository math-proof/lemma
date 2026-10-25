/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Structure.v1.Atlas.EllipticCurves.code.AlgebraicGeometry
open MvPolynomial Set


noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable {σ : Type*}

/-- The equivalence relation on `HomogeneousRationalFunction`s used to define
the function field of a projective curve: `p₁ ∼ p₂` iff
`p₁.num * p₂.den - p₂.num * p₁.den ∈ (f)`. -/
def HomogeneousRationalFunction.Equiv (k : Type*) [CommRing k]
    (f : MvPolynomial (Fin 3) k) :
    HomogeneousRationalFunction k f → HomogeneousRationalFunction k f → Prop :=
  fun p₁ p₂ => p₁.num * p₂.den - p₂.num * p₁.den ∈
    Ideal.span ({f} : Set (MvPolynomial (Fin 3) k))

/-- The setoid on `HomogeneousRationalFunction`s built from `Equiv`. Reflexivity,
symmetry, and transitivity use that `(f)` is a prime ideal (since `f` is
irreducible), so denominators behave well. -/
def projectiveFunctionFieldSetoid {k : Type*} [Field k]
    (f : MvPolynomial (Fin 3) k) [Fact (Irreducible f)] :
    Setoid (HomogeneousRationalFunction k f) where
  r := HomogeneousRationalFunction.Equiv k f
  iseqv := {
    refl := fun p => by
      simp [HomogeneousRationalFunction.Equiv, sub_self]
    symm := fun {p₁ p₂} h => by
      simp only [HomogeneousRationalFunction.Equiv] at *
      rwa [show p₂.num * p₁.den - p₁.num * p₂.den =
        -(p₁.num * p₂.den - p₂.num * p₁.den) from by ring,
        Ideal.neg_mem_iff]
    trans := fun {p₁ p₂ p₃} h12 h23 => by
      simp only [HomogeneousRationalFunction.Equiv] at *
      have h12' := Ideal.mul_mem_right p₃.den _ h12
      have h23' := Ideal.mul_mem_right p₁.den _ h23
      have hsum := Ideal.add_mem _ h12' h23'
      have hrw : (p₁.num * p₂.den - p₂.num * p₁.den) * p₃.den +
          (p₂.num * p₃.den - p₃.num * p₂.den) * p₁.den =
          p₂.den * (p₁.num * p₃.den - p₃.num * p₁.den) := by ring
      rw [hrw] at hsum
      have hprime : (Ideal.span ({f} : Set (MvPolynomial (Fin 3) k))).IsPrime := by
        rw [Ideal.span_singleton_prime]
        · exact (Fact.out : Irreducible f).prime
        · exact (Fact.out : Irreducible f).ne_zero
      exact (hprime.mem_or_mem hsum).resolve_left p₂.den_not_in_ideal
  }

/-- The function field of the projective curve cut out by an irreducible
`f ∈ k[x, y, z]`: the quotient of homogeneous rational functions by the
equivalence relation `projectiveFunctionFieldSetoid f`. -/
def functionField (k : Type*) [Field k]
    (f : MvPolynomial (Fin 3) k) [Fact (Irreducible f)] :=
  Quotient (projectiveFunctionFieldSetoid f)

/-- The canonical map sending a homogeneous rational function to its class in
the function field. -/
def functionField.mk {k : Type*} [Field k]
    {f : MvPolynomial (Fin 3) k} [Fact (Irreducible f)]
    (p : HomogeneousRationalFunction k f) : functionField k f :=
  Quotient.mk (projectiveFunctionFieldSetoid f) p

end
