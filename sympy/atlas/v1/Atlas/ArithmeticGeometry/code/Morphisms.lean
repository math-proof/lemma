/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Varieties
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Theorem1324
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Basic
import Mathlib.Topology.Order

noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- A nonzero $(n+1)$-tuple of coordinates in $\bar k$, the underlying data of
a point of projective $n$-space before quotienting by rescaling. -/
def ProjectivePoint (n : ℕ) : Type _ :=
  {v : Fin (n + 1) → AlgebraicClosure k // v ≠ 0}

/-- The equivalence relation on $\bar k^{n+1} \setminus \{0\}$ identifying two
nonzero tuples that differ by a nonzero scalar; the quotient is projective
$n$-space $\mathbb{P}^n(\bar k)$. -/
def projectiveSetoid (n : ℕ) : Setoid (ProjectivePoint k n) where
  r v w := ∃ c : AlgebraicClosure k, c ≠ 0 ∧ ∀ i, v.1 i = c * w.1 i
  iseqv := {
    refl := fun v => ⟨1, one_ne_zero, fun i => by ring⟩
    symm := fun ⟨c, hc, h⟩ =>
      ⟨c⁻¹, inv_ne_zero hc, fun i => by rw [h i, inv_mul_cancel_left₀ hc]⟩
    trans := fun ⟨c, hc, h1⟩ ⟨d, hd, h2⟩ =>
      ⟨c * d, mul_ne_zero hc hd, fun i => by rw [h1, h2]; ring⟩
  }

/-- Projective $n$-space $\mathbb{P}^n(\bar k)$ over the algebraic closure of
$k$, defined as the quotient of $\bar k^{n+1}\setminus\{0\}$ by the scaling
equivalence relation. -/
def ProjectiveSpace_k (n : ℕ) : Type _ :=
  Quotient (projectiveSetoid k n)

/-- The set of $k$-rational points $\mathbb{P}^n(k) \subseteq \mathbb{P}^n(\bar k)$:
those projective points admitting a representative all of whose coordinates lie
in the image of $k \hookrightarrow \bar k$. -/
def ProjectiveSpace_k.kRationalPoints (n : ℕ) : Set (ProjectiveSpace_k k n) :=
  {p | ∃ v : ProjectivePoint k n, Quotient.mk (projectiveSetoid k n) v = p ∧
    ∀ i : Fin (n + 1), ∃ a : k, algebraMap k (AlgebraicClosure k) a = v.1 i}

/-- A homogeneous polynomial of some degree $d$ in $n+1$ variables over $\bar k$:
the package of an underlying polynomial together with the degree witness. -/
structure HomogPoly (n : ℕ) where
  poly : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k)
  deg : ℕ
  isHomog : poly.IsHomogeneous deg

/-- Rescaling identity for homogeneous polynomials:
$f(cv_0, \ldots, cv_n) = c^d \cdot f(v_0, \ldots, v_n)$, where $d$ is the
homogeneous degree of $f$. -/
lemma homog_eval_rescale (n : ℕ) (f : HomogPoly k n)
    (c : AlgebraicClosure k) (v : Fin (n + 1) → AlgebraicClosure k) :
    eval (fun i => c * v i) f.poly = c ^ f.deg * eval v f.poly := by
  have := HomogeneousPolynomial.isHomogeneous_eval_smul f.poly f.deg f.isHomog c v
  exact this

/-- The projective vanishing set $V(S) \subseteq \mathbb{P}^n(\bar k)$ of a
family of homogeneous polynomials $S$: those points where every $f \in S$
vanishes (the rescaling identity ensures the condition descends to the
quotient). -/
def ProjVanishingSet (n : ℕ) (S : Set (HomogPoly k n)) : Set (ProjectiveSpace_k k n) :=
  {P | P.liftOn
    (fun v => ∀ f ∈ S, eval v.1 f.poly = 0)
    (by
      intro a b ⟨c, hc, hcab⟩
      simp only [eq_iff_iff]
      have ha_eq : a.1 = (fun i => c * b.1 i) := funext (hcab ·)
      constructor <;> intro h f hf
      · have heval := h f hf
        rw [show eval a.1 f.poly = c ^ f.deg * eval b.1 f.poly from by
            rw [ha_eq]; exact homog_eval_rescale k n f c b.1] at heval
        exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hc)
      · rw [show eval a.1 f.poly = c ^ f.deg * eval b.1 f.poly from by
            rw [ha_eq]; exact homog_eval_rescale k n f c b.1,
          h f hf, mul_zero])}

/-- A subset of $\mathbb{P}^n(\bar k)$ is *projectively algebraic* if it arises
as the common vanishing locus of some family of homogeneous polynomials. -/
def IsProjectiveAlgSet (n : ℕ) (V : Set (ProjectiveSpace_k k n)) : Prop :=
  ∃ S : Set (HomogPoly k n), V = ProjVanishingSet k n S

/-- The collection of all projectively algebraic subsets of $\mathbb{P}^n(\bar k)$;
its members serve as the closed sets of the projective Zariski topology. -/
def projAlgSetsCollection (n : ℕ) : Set (Set (ProjectiveSpace_k k n)) :=
  {V | IsProjectiveAlgSet k n V}

/-- The empty set is projectively algebraic: it is cut out by the polynomial
$1$, which has no zeros. -/
lemma projAlgSets_empty_mem (n : ℕ) : ∅ ∈ projAlgSetsCollection k n := by
  refine ⟨{⟨1, 0, MvPolynomial.isHomogeneous_one _ _⟩}, ?_⟩
  ext P
  simp only [Set.mem_empty_iff_false, ProjVanishingSet, Set.mem_setOf_eq, false_iff]
  obtain ⟨v, rfl⟩ := P.exists_rep
  simp only [Quotient.liftOn_mk]
  intro h
  exact absurd (h ⟨1, 0, MvPolynomial.isHomogeneous_one _ _⟩ (Set.mem_singleton _)) (by simp)

/-- Arbitrary intersections of projectively algebraic sets are projectively
algebraic: union the underlying homogeneous polynomial families. -/
lemma projAlgSets_sInter_mem (n : ℕ) (A : Set (Set (ProjectiveSpace_k k n)))
    (hA : A ⊆ projAlgSetsCollection k n) :
    ⋂₀ A ∈ projAlgSetsCollection k n := by
  choose S hS using fun V (hV : V ∈ A) => hA hV
  refine ⟨⋃ (V : Set (ProjectiveSpace_k k n)) (_ : V ∈ A), S V ‹_›, ?_⟩
  ext P
  simp only [Set.mem_sInter, ProjVanishingSet, Set.mem_setOf_eq]
  obtain ⟨v, rfl⟩ := P.exists_rep
  simp only [Quotient.liftOn_mk]
  constructor
  · intro h f hf
    obtain ⟨V, hV, hfS⟩ := Set.mem_iUnion₂.mp hf
    have := h V hV
    rw [hS V hV, ProjVanishingSet, Set.mem_setOf_eq, Quotient.liftOn_mk] at this
    exact this f hfS
  · intro h V hV
    rw [hS V hV, ProjVanishingSet, Set.mem_setOf_eq, Quotient.liftOn_mk]
    exact fun f hfS => h f (Set.mem_iUnion₂.mpr ⟨V, hV, hfS⟩)

/-- The union of two projectively algebraic sets is projectively algebraic:
take pairwise products of the defining homogeneous polynomials. -/
lemma projAlgSets_union_mem (n : ℕ)
    (A : Set (ProjectiveSpace_k k n)) (hA : A ∈ projAlgSetsCollection k n)
    (B : Set (ProjectiveSpace_k k n)) (hB : B ∈ projAlgSetsCollection k n) :
    A ∪ B ∈ projAlgSetsCollection k n := by
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, rfl⟩ := hB
  let ST : Set (HomogPoly k n) :=
    {fg | ∃ f ∈ S, ∃ g ∈ T,
      fg = ⟨f.poly * g.poly, f.deg + g.deg, f.isHomog.mul g.isHomog⟩}
  refine ⟨ST, ?_⟩
  ext P
  simp only [Set.mem_union, ProjVanishingSet, Set.mem_setOf_eq]
  obtain ⟨v, rfl⟩ := P.exists_rep
  simp only [Quotient.liftOn_mk]
  constructor
  · rintro (hS | hT) fg ⟨f, hf, g, hg, rfl⟩
    · simp [map_mul, hS f hf]
    · simp [map_mul, hT g hg]
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨⟨f, hf, hfP⟩, ⟨g, hg, hgP⟩⟩ := hc
    have hmem : (⟨f.poly * g.poly, f.deg + g.deg,
        f.isHomog.mul g.isHomog⟩ : HomogPoly k n) ∈ ST :=
      ⟨f, hf, g, hg, rfl⟩
    have := h _ hmem
    simp only at this
    rw [map_mul] at this
    exact (mul_eq_zero.mp this).elim hfP hgP

/-- The *projective Zariski topology* on $\mathbb{P}^n(\bar k)$: closed sets
are exactly the projectively algebraic subsets. -/
@[reducible]
def zariskiTopologyProjective (n : ℕ) : TopologicalSpace (ProjectiveSpace_k k n) :=
  TopologicalSpace.ofClosed (projAlgSetsCollection k n)
    (projAlgSets_empty_mem k n)
    (projAlgSets_sInter_mem k n)
    (projAlgSets_union_mem k n)

/-- **Definition 14.6.** An *affine isomorphism* $X \cong Y$ consists of mutually
inverse affine morphisms $X \to Y$ and $Y \to X$. -/
structure AffineIsomorphism {m n : ℕ}
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) where
  toMorphism : AffineMorphism k m n X Y
  invMorphism : AffineMorphism k n m Y X
  left_inv : ∀ Q ∈ Y, toMorphism.toFun k (invMorphism.toFun k Q) = Q
  right_inv : ∀ P ∈ X, invMorphism.toFun k (toMorphism.toFun k P) = P

/-- Two algebraic subsets $X$ and $Y$ are *isomorphic as affine varieties* if
there exists an affine isomorphism between them. -/
def AreIsomorphic {m n : ℕ}
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) : Prop :=
  Nonempty (AffineIsomorphism k X Y)

/-- An affine morphism $f$ is an *isomorphism* iff it admits an affine inverse
$g$ in the morphism sense (mutually inverse on the underlying point sets). -/
def AffineMorphism.IsIsomorphism {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (f : AffineMorphism k m n X Y) : Prop :=
  ∃ g : AffineMorphism k n m Y X,
    (∀ Q ∈ Y, f.toFun k (g.toFun k Q) = Q) ∧
    (∀ P ∈ X, g.toFun k (f.toFun k P) = P)


/-- Reflexivity for the isomorphism relation: the identity morphism realises
$X \cong X$. -/
def AffineIsomorphism.refl {n : ℕ} (X : Set (AffineSpace_k k n)) :
    AffineIsomorphism k X X where
  toMorphism := AffineMorphism.id k X
  invMorphism := AffineMorphism.id k X
  left_inv Q _ := by simp [AffineMorphism.toFun_id]
  right_inv P _ := by simp [AffineMorphism.toFun_id]

/-- Symmetry: an isomorphism $X \cong Y$ inverts to an isomorphism $Y \cong X$. -/
def AffineIsomorphism.symm {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineIsomorphism k X Y) : AffineIsomorphism k Y X where
  toMorphism := φ.invMorphism
  invMorphism := φ.toMorphism
  left_inv := φ.right_inv
  right_inv := φ.left_inv

/-- Transitivity: composition of two affine isomorphisms is an affine
isomorphism. -/
def AffineIsomorphism.trans {m n r : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    {Z : Set (AffineSpace_k k r)}
    (φ : AffineIsomorphism k X Y) (ψ : AffineIsomorphism k Y Z) :
    AffineIsomorphism k X Z where
  toMorphism := ψ.toMorphism.comp k φ.toMorphism
  invMorphism := φ.invMorphism.comp k ψ.invMorphism
  left_inv Q hQ := by
    have h1 : (ψ.toMorphism.comp k φ.toMorphism).toFun k
        ((φ.invMorphism.comp k ψ.invMorphism).toFun k Q)
        = ψ.toMorphism.toFun k (φ.toMorphism.toFun k
            (φ.invMorphism.toFun k (ψ.invMorphism.toFun k Q))) := by
      simp only [AffineMorphism.toFun_comp]
    have h2 : ψ.invMorphism.toFun k Q ∈ Y := ψ.invMorphism.maps_to Q hQ
    rw [h1, φ.left_inv _ h2, ψ.left_inv _ hQ]
  right_inv P hP := by
    have h1 : (φ.invMorphism.comp k ψ.invMorphism).toFun k
        ((ψ.toMorphism.comp k φ.toMorphism).toFun k P)
        = φ.invMorphism.toFun k (ψ.invMorphism.toFun k
            (ψ.toMorphism.toFun k (φ.toMorphism.toFun k P))) := by
      simp only [AffineMorphism.toFun_comp]
    have h2 : φ.toMorphism.toFun k P ∈ Y := φ.toMorphism.maps_to P hP
    rw [h1, ψ.right_inv _ h2, φ.right_inv _ hP]


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


/-- A ring homomorphism between coordinate rings over $\bar k$ is *$\bar k$-algebra
preserving* if it fixes the scalar subring, i.e. sends $\bar r \in \bar k[Y]$ to
$\bar r \in \bar k[X]$ for every $r \in \bar k$. -/
def IsAlgHomBar {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (θ : AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X) : Prop :=
  ∀ r : AlgebraicClosure k,
    θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) =
    Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r)

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
