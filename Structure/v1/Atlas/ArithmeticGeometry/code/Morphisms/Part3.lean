/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part5


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- **Theorem 14.8 (data).** A bundle of data witnessing the contravariant
equivalence between affine varieties (and their morphisms) and their coordinate
rings (with $\bar k$-algebra homomorphisms): a functor in each direction
together with round-trip identities. -/
structure ContravariantEquivalenceData (k : Type*) [Field k] (m n : ℕ)
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) where
  coordRingFunctor :
    AffineMorphism k m n X Y → (AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X)
  coordRingFunctor_isAlgHom :
    ∀ (φ : AffineMorphism k m n X Y), IsAlgHomBar k (coordRingFunctor φ)
  varietyFunctor :
    {θ : AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X} →
    IsAlgHomBar k θ → AffineMorphism k m n X Y
  functoriality : ∀ {r : ℕ} {Z : Set (AffineSpace_k k r)}
    (ψ : AffineMorphism k n r Y Z) (φ : AffineMorphism k m n X Y),
    (ψ.comp k φ).pullback k = (φ.pullback k).comp (ψ.pullback k)
  roundTrip_algHom : ∀ (θ : AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X)
    (hθ : IsAlgHomBar k θ),
    ∀ (g : MvPolynomial (Fin n) (AlgebraicClosure k))
      (P : AffineSpace_k k m) (hP : P ∈ X),
      evalOnCoordRing k X P hP
        (coordRingFunctor (varietyFunctor hθ)
          (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) =
      evalOnCoordRing k X P hP
        (θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g))
  roundTrip_morphism : ∀ (φ : AffineMorphism k m n X Y)
    (hφ : IsAlgHomBar k (coordRingFunctor φ)),
    ∀ (P : AffineSpace_k k m) (hP : P ∈ X),
      (varietyFunctor hφ).toFun k P = φ.toFun k P

end
