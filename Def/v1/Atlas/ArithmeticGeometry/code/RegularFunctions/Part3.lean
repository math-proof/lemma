/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Opposites
import Structure.v1.Atlas.ArithmeticGeometry.code.RegularFunctions
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section RegularFunctions

variable {k}

variable {n : ℕ} {X : Set (Fin n → AlgebraicClosure k)}

variable [hdom : IsDomain (AffineCoordinateRingBar X)]

/-- The *domain of definition* of a rational map (as a tuple of rational functions):
the set of points of $X$ where every component is regular. -/
def rationalMapDomain
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) :
    Set (Fin m → AlgebraicClosure k) :=
  {P : Fin m → AlgebraicClosure k | ∃ (hP : P ∈ X), IsTupleRegularAt φ P hP}


/-- A rational map $\varphi$ is *regular* (a morphism of affine varieties) if it is
regular at every point of $X$. -/
def IsRegularRationalMap
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) : Prop :=
  ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X), IsTupleRegularAt φ P hP


end RationalMaps

section DominantAndBirational

variable {k : Type*} [Field k]

open MvPolynomial

/-- The *Zariski closure* of a subset $S \subseteq \bar k^n$: the smallest algebraic
set containing $S$, namely $\mathcal{V}(\mathcal{I}(S))$. -/
def zariskiClosure {n : ℕ}
    (S : Set (Fin n → AlgebraicClosure k)) :
    Set (Fin n → AlgebraicClosure k) :=
  AlgebraicSet k n ((idealOfAlgebraicSet S : Ideal _) : Set _)


/-- The set-theoretic image of a rational map (defined on its domain): the set of all
$Q \in \bar k^{n_\mathrm{cod}}$ that arise as the value of $\varphi$ at some point of
$\mathrm{dom}(\varphi)$. -/
def rationalMapImage {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) :
    Set (Fin n_cod → AlgebraicClosure k) :=
  {Q : Fin n_cod → AlgebraicClosure k |
    ∃ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
      (hreg : IsTupleRegularAt φ P hP),
      evalTupleAt φ P hP hreg = Q}

/-- Definition 15.7 (dominant rational map). A rational map $\varphi : X \dashrightarrow Y$
is *dominant* if its image is Zariski-dense in $Y$, i.e. the Zariski closure of the image
equals $Y$. -/
def IsDominantRationalMap {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (Y : Set (Fin n_cod → AlgebraicClosure k))
    (φ : AffineRationalMap X Y) : Prop :=
  zariskiClosure (rationalMapImage φ.components) = Y

/-- The *composition domain* of $\psi \circ \varphi$ where $\varphi : X \dashrightarrow Y$
and $\psi : Y \dashrightarrow X$: the set of points $P \in X$ where $\varphi$ is regular
at $P$, $\varphi(P) \in Y$, and $\psi$ is regular at $\varphi(P)$. -/
def compositionDomain {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (ψ : AffineRationalMap Y X) :
    Set (Fin m → AlgebraicClosure k) :=
  {P : Fin m → AlgebraicClosure k |
    ∃ (hP : P ∈ X) (hregφ : IsTupleRegularAt φ.components P hP),
      ∃ (hQ : evalTupleAt φ.components P hP hregφ ∈ Y),
        IsTupleRegularAt ψ.components
          (evalTupleAt φ.components P hP hregφ) hQ}

/-- Pointwise evaluation of the composition $\psi \circ \varphi$ at $P \in
\mathrm{compositionDomain}(\varphi, \psi)$: returns $\psi(\varphi(P)) \in \bar k^m$. -/
noncomputable def evalCompositionAt {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (ψ : AffineRationalMap Y X)
    (P : Fin m → AlgebraicClosure k)
    (hcomp : P ∈ compositionDomain φ ψ) :
    Fin m → AlgebraicClosure k :=
  let hP := hcomp.choose
  let hregφ := hcomp.choose_spec.choose
  let hQ := hcomp.choose_spec.choose_spec.choose
  let hregψ := hcomp.choose_spec.choose_spec.choose_spec
  evalTupleAt ψ.components
    (evalTupleAt φ.components P hP hregφ) hQ hregψ

/-- Definition 15.10 (birational equivalence). Two affine algebraic sets $X$ and $Y$
are *birationally equivalent* if there exist dominant rational maps
$\varphi : X \dashrightarrow Y$ and $\psi : Y \dashrightarrow X$ whose compositions (on
their composition domains) agree with the respective identities. -/
def AreBirationallyEquivalent {m n_cod : ℕ}
    (X : Set (Fin m → AlgebraicClosure k))
    (Y : Set (Fin n_cod → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)] : Prop :=
  ∃ (φ : AffineRationalMap X Y) (ψ : AffineRationalMap Y X),
    IsDominantRationalMap Y φ ∧
    IsDominantRationalMap X ψ ∧
    (∀ (P : Fin m → AlgebraicClosure k)
       (hcomp : P ∈ compositionDomain φ ψ),
       evalCompositionAt φ ψ P hcomp = P) ∧
    (∀ (Q : Fin n_cod → AlgebraicClosure k)
       (hcomp : Q ∈ compositionDomain ψ φ),
       evalCompositionAt ψ φ Q hcomp = Q)

end DominantAndBirational

section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

/-- A ring homomorphism $\theta : \bar k(Y) \to \bar k(X)$ is a *$\bar k$-algebra
homomorphism of function fields* if it fixes the scalars from $\bar k$ (under the
canonical inclusions $\bar k \hookrightarrow \bar k[Y] \hookrightarrow \bar k(Y)$). -/
def IsKbarFunctionFieldHom {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X)) : Prop :=
  ∀ r : AlgebraicClosure k,
    θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r))) =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r))

/-- The substitution homomorphism $\bar k[Y_1, \dots, Y_{n_\mathrm{cod}}] \to \bar k(X)$
sending each coordinate $Y_i$ to the corresponding component $\varphi_i \in \bar k(X)$.
This is the first step in building the pullback induced by a rational map. -/
noncomputable def dominantPullbackSubstHom
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) :
    MvPolynomial (Fin n_cod) (AlgebraicClosure k) →+*
    FractionRing (AffineCoordinateRingBar X) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
      ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C))
    φ

end Theorem158
