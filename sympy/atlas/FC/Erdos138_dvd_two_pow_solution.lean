/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos138_dvd_two_pow_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


open Nat Filter

namespace Erdos138


def monoAP_guarantee_set (r k : ℕ) : Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k}


noncomputable def monoAPNumber (r k : ℕ) : ℕ := sInf (monoAP_guarantee_set r k)


noncomputable abbrev W : ℕ → ℕ := monoAPNumber 2

def erdos_138_variants_dvd_two_pow_statement : Prop := atTop.Tendsto (fun k => ((W k : ℚ)/ (2 ^ k))) atTop

abbrev BinaryGaloisField (p : ℕ) := GaloisField 2 p

noncomputable def primitiveBinaryUnit (p : ℕ) : (BinaryGaloisField p)ˣ :=
  Classical.choose (IsCyclic.exists_generator (α := (BinaryGaloisField p)ˣ))

noncomputable def recurrenceOfMonic {R : Type*} [CommRing R]
    (P : Polynomial R) : LinearRecurrence R where
  order := P.natDegree
  coeffs i := -P.coeff i

noncomputable def recurrenceMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (E : LinearRecurrence R) : LinearRecurrence S where
  order := E.order
  coeffs i := f (E.coeffs i)

noncomputable def combinedMinpoly (S : Finset ℕ) (d : ℕ) : Polynomial (ZMod 2) :=
  ∏ p ∈ S, minpoly (ZMod 2)
    ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d)

noncomputable def combinedDifference (S : Finset ℕ) (a d i : ℕ) : ZMod 2 :=
  ∑ p ∈ S, (Algebra.trace (ZMod 2) (BinaryGaloisField p))
    (((primitiveBinaryUnit p : BinaryGaloisField p) ^ a *
      ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d - 1)) *
      ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d) ^ i)

noncomputable def binaryMSequence (p : ℕ) (n : ℕ) : ZMod 2 :=
  (Algebra.trace (ZMod 2) (BinaryGaloisField p))
    ((primitiveBinaryUnit p : BinaryGaloisField p) ^ n)

noncomputable def combinedZSequence (S : Finset ℕ) (n : ℕ) : ZMod 2 :=
  ∑ p ∈ S, binaryMSequence p n

noncomputable def combinedMSequence (S : Finset ℕ) (n : ℕ) : Fin 2 :=
  (ZMod.finEquiv 2).symm (∑ p ∈ S, binaryMSequence p n)

noncomputable def componentDifference (p a d i : ℕ) : ZMod 2 :=
  (Algebra.trace (ZMod 2) (BinaryGaloisField p))
    (((primitiveBinaryUnit p : BinaryGaloisField p) ^ a *
      ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d - 1)) *
      ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d) ^ i)
