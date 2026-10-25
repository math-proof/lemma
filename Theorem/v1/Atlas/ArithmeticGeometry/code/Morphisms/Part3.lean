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
import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part4


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- Compatibility lemma for the contravariant equivalence: when a ring
homomorphism $\theta: \bar k[Y] \to \bar k[X]$ is induced by polynomial maps
$\mathrm{polys}$, the pullback of the resulting morphism agrees with $\theta$
upon evaluation on the coordinate ring. -/
theorem pullback_of_induced_morphism_eq {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (hY : Y = AlgebraicSet k n (idealOfAlgebraicSet Y : Set _))
    (θ : AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X)
    (hθ_alg : ∀ r : AlgebraicClosure k,
      θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) =
      Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r))
    (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (hmaps : ∀ P ∈ X, polyMapEval k m n polys P ∈ Y)
    (heval : ∀ (g : MvPolynomial (Fin n) (AlgebraicClosure k))
      (P : AffineSpace_k k m) (hP : P ∈ X),
      evalOnCoordRing k X P hP (θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) =
      MvPolynomial.eval (polyMapEval k m n polys P) g) :
    ∀ (g : MvPolynomial (Fin n) (AlgebraicClosure k))
      (P : AffineSpace_k k m) (hP : P ∈ X),
      evalOnCoordRing k X P hP
        ((AffineMorphism.mk polys hmaps).pullback k
          (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) =
      evalOnCoordRing k X P hP
        (θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) := by


  intro g P hP
  have lhs : evalOnCoordRing k X P hP
      ((AffineMorphism.mk polys hmaps).pullback k
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) =
      MvPolynomial.eval P ((MvPolynomial.bind₁ polys) g) := rfl
  have rhs : evalOnCoordRing k X P hP
      (θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) =
      MvPolynomial.eval (polyMapEval k m n polys P) g := heval g P hP
  rw [lhs, rhs]
  exact eval_bind₁_eq_eval_polyMapEval k P polys g

/-- Conversely: if the pullback of an affine morphism $\varphi$ is realised by
polynomial maps `polys'`, then `polys'` agrees with `φ.polys` on the underlying
point set. -/
theorem induced_morphism_of_pullback_eq {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (hY : Y = AlgebraicSet k n (idealOfAlgebraicSet Y : Set _))
    (φ : AffineMorphism k m n X Y)
    (hφ_alg : ∀ r : AlgebraicClosure k,
      φ.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) =
      Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r))
    (polys' : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (hmaps' : ∀ P ∈ X, polyMapEval k m n polys' P ∈ Y)
    (heval' : ∀ (g : MvPolynomial (Fin n) (AlgebraicClosure k))
      (P : AffineSpace_k k m) (hP : P ∈ X),
      evalOnCoordRing k X P hP
        (φ.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) =
      MvPolynomial.eval (polyMapEval k m n polys' P) g) :
    ∀ (P : AffineSpace_k k m) (hP : P ∈ X),
      polyMapEval k m n polys' P = φ.toFun k P := by


  intro P hP
  funext j
  have h := heval' (MvPolynomial.X j) P hP


  change MvPolynomial.eval P (polys' j) = MvPolynomial.eval P (φ.polys j)

  have lhs_h : evalOnCoordRing k X P hP
      (φ.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j))) =
      MvPolynomial.eval P ((MvPolynomial.bind₁ φ.polys) (MvPolynomial.X j)) := rfl
  rw [lhs_h] at h
  rw [MvPolynomial.bind₁_X_right] at h
  rw [MvPolynomial.eval_X] at h
  exact h.symm


end
