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
import Structure.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part3


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- **Corollary 14.9.** Assuming $Y = V(I(Y))$, the construction
$\varphi \mapsto \varphi^*$ together with its inverse $\theta \mapsto \theta^*$
exhibits a contravariant equivalence between the category of affine morphisms
$X \to Y$ and the category of $\bar k$-algebra homomorphisms
$\bar k[Y] \to \bar k[X]$. -/
noncomputable def corollary_14_9_categorical_equiv {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (hY : Y = AlgebraicSet k n (idealOfAlgebraicSet Y : Set _)) :
    ContravariantEquivalenceData k m n X Y where
  coordRingFunctor φ := φ.pullback k
  coordRingFunctor_isAlgHom φ r := by
    show φ.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) =
      Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r)
    simp only [AffineMorphism.pullback]
    erw [Ideal.Quotient.lift_mk, RingHom.comp_apply, MvPolynomial.bind₁_C_right]

  varietyFunctor hθ :=
    let polys := Classical.choose (algebraHom_induces_morphism k hY _ hθ)
    let hspec := Classical.choose_spec (algebraHom_induces_morphism k hY _ hθ)
    AffineMorphism.mk polys hspec.1
  functoriality ψ φ := AffineMorphism.pullback_comp k ψ φ
  roundTrip_algHom θ hθ g P hP := by
    set polys := Classical.choose (algebraHom_induces_morphism k hY θ hθ)
    set hspec := Classical.choose_spec (algebraHom_induces_morphism k hY θ hθ)
    exact pullback_of_induced_morphism_eq k hY θ hθ polys hspec.1 hspec.2 g P hP
  roundTrip_morphism φ hφ P hP := by
    set polys := Classical.choose (algebraHom_induces_morphism k hY (φ.pullback k) hφ)
    set hspec := Classical.choose_spec (algebraHom_induces_morphism k hY (φ.pullback k) hφ)
    exact induced_morphism_of_pullback_eq k hY φ hφ polys hspec.1 hspec.2 P hP

end

section PrimeSpectrumZariski

open PrimeSpectrum

variable {R : Type*} [CommSemiring R]


end PrimeSpectrumZariski

variable (k : Type*) [Field k]

open AffineParts ProjectiveDimension

/-- A family of homogeneous polynomials $S$ defines a *projective variety* if
its projective vanishing locus is a projective variety in the structural sense. -/
def IsProjectiveVarietyOfPolys
    {n : ℕ} (S : Set (MvPolynomial (Fin (n + 1)) (AlgebraicClosure k))) : Prop :=
  ProjectiveVarietyDef.IsProjectiveVariety (AlgebraicClosure k)
    (AffineParts.projectiveZeroLocus (AlgebraicClosure k) S)

/-- Axiom: the vanishing ideal of an affine chart of a projective variety is
the image of a homogeneous prime ideal under the dehomogenization map. -/

section DefinedOverK

variable {k : Type*} [Field k]

/-- An affine morphism is *defined over $k$* if each of its component
polynomials lies in the image of $k[X_1, \ldots, X_m] \hookrightarrow
\bar k[X_1, \ldots, X_m]$. -/
def AffineMorphism.IsDefinedOverK {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineMorphism k m n X Y) : Prop :=
  ∀ j : Fin n, φ.polys j ∈ Set.range (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))

/-- An affine isomorphism is *defined over $k$* if both its forward and inverse
morphisms are. -/
def AffineIsomorphism.IsDefinedOverK {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineIsomorphism k X Y) : Prop :=
  φ.toMorphism.IsDefinedOverK ∧ φ.invMorphism.IsDefinedOverK

/-- Two affine varieties are *isomorphic over $k$* if there exists an affine
isomorphism between them which is defined over $k$. -/
def AreIsomorphicOverK {m n : ℕ}
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) : Prop :=
  ∃ φ : AffineIsomorphism k X Y, φ.IsDefinedOverK

end DefinedOverK

noncomputable section Cor1412

open MvPolynomial

variable {k : Type*} [Field k]

/-- The *pullback over $k$* of an affine morphism $\varphi$ that is defined
over $k$: the induced $k$-algebra map $k[Y] \to k[X]$ between $k$-coordinate
rings. -/
def AffineMorphism.pullbackOverK {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineMorphism k m n X Y)
    (hφ : φ.IsDefinedOverK) :
    AffineCoordinateRing Y →+* AffineCoordinateRing X :=
  let polysK : Fin n → MvPolynomial (Fin m) k := fun j => (hφ j).choose
  let hpolysK : ∀ j, φ.polys j = MvPolynomial.map (algebraMap k (AlgebraicClosure k)) (polysK j) :=
    fun j => ((hφ j).choose_spec).symm
  Ideal.Quotient.lift (idealOverK Y)
    ((Ideal.Quotient.mk (idealOverK X)).comp
      (MvPolynomial.bind₁ polysK).toRingHom)
    (fun f hf => by
      simp only [AlgHom.toRingHom_eq_coe]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (bind₁_mem_idealOverK_of_maps_to φ.polys φ.maps_to polysK hpolysK hf))


end Cor1412
