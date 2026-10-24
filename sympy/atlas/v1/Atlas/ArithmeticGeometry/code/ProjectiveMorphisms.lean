/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Mathlib.Algebra.MvPolynomial.Monad

noncomputable section

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- A homogeneous representative of a projective regular function: a pair of homogeneous polynomials $(\text{num}, \text{den})$ of the same degree on $\mathbb{P}^n$, with $\text{den} \neq 0$, representing the rational function $\text{num}/\text{den}$. -/
structure HomogeneousRep (n : ℕ) (k : Type*) [Field k] where
  num : MvPolynomial (Fin (n + 1)) k
  den : MvPolynomial (Fin (n + 1)) k
  deg : ℕ
  num_homog : num.IsHomogeneous deg
  den_homog : den.IsHomogeneous deg
  den_ne_zero : den ≠ 0

/-- A homogeneous representative is defined at a projective point $P$ if its denominator does not vanish at $P$. -/
def HomogeneousRep.isDefinedAt (r : HomogeneousRep n k)
    (P : ℙ k (Fin (n + 1) → k)) : Prop :=
  eval P.rep r.den ≠ 0

/-- Evaluate a homogeneous representative $\text{num}/\text{den}$ at a projective point $P$. Well-defined when the denominator is nonzero. -/
noncomputable def HomogeneousRep.evalAt (r : HomogeneousRep n k)
    (P : ℙ k (Fin (n + 1) → k)) : k :=
  eval P.rep r.num / eval P.rep r.den

/-- Two homogeneous representatives are equivalent on a set $X$ iff $\text{num}_1 \cdot \text{den}_2 - \text{num}_2 \cdot \text{den}_1$ vanishes on $X$ (i.e., they define the same rational function on $X$). -/
def HomogeneousRep.equivOn (r₁ r₂ : HomogeneousRep n k)
    (X : Set (ℙ k (Fin (n + 1) → k))) : Prop :=
  ∀ P ∈ X, eval P.rep (r₁.num * r₂.den - r₂.num * r₁.den) = 0

/-- Reflexivity: any homogeneous representative is equivalent to itself on $X$. -/
theorem HomogeneousRep.equivOn_refl (r : HomogeneousRep n k)
    (X : Set (ℙ k (Fin (n + 1) → k))) :
    r.equivOn k r X := by
  intro P _
  simp [sub_self]

/-- Symmetry of `equivOn`: if $r_1 \sim r_2$ on $X$ then $r_2 \sim r_1$ on $X$. -/
theorem HomogeneousRep.equivOn_symm (r₁ r₂ : HomogeneousRep n k)
    (X : Set (ℙ k (Fin (n + 1) → k)))
    (h : r₁.equivOn k r₂ X) :
    r₂.equivOn k r₁ X := by
  intro P hP
  have hval := h P hP
  simp only [map_sub, map_mul] at hval ⊢
  have := neg_eq_zero.mpr hval
  rw [neg_sub] at this
  exact this

/-- A projective rational function on a set $X \subseteq \mathbb{P}^n_k$: an equivalence class of homogeneous representatives, packaged as a maximal nonempty set of mutually equivalent `HomogeneousRep`s. -/
structure ProjectiveRatFun (n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (n + 1) → k))) where
  reps : Set (HomogeneousRep n k)
  reps_nonempty : reps.Nonempty
  reps_equiv : ∀ r₁ ∈ reps, ∀ r₂ ∈ reps, HomogeneousRep.equivOn k r₁ r₂ X
  reps_maximal : ∀ r, (∃ r₀ ∈ reps, HomogeneousRep.equivOn k r r₀ X) → r ∈ reps

/-- The denominator of any representative of a projective rational function does not vanish identically on $X$ (else the function would be undefined everywhere). -/
def ProjectiveRatFun.IsRegularAt
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X)
    (P : ℙ k (Fin (n + 1) → k))
    (_hP : P ∈ X) : Prop :=
  ∃ rep ∈ r.reps, rep.isDefinedAt k P

/-- The regular domain (locus of regularity) of a projective rational function: all points of $X$ where some representative is defined. -/
def ProjectiveRatFun.regularDomain
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  {P ∈ X | ∃ rep ∈ r.reps, rep.isDefinedAt k P}

/-- Evaluate a projective rational function $r$ at a point $P$ in its regular domain by choosing any representative defined at $P$ and evaluating it. -/
noncomputable def ProjectiveRatFun.evalAt
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X)
    (P : ℙ k (Fin (n + 1) → k))
    (hP : P ∈ r.regularDomain k) : k :=
  hP.2.choose.evalAt k P

/-- A tuple representative of a rational map $X \dashrightarrow Y$ between projective varieties: an $(n+1)$-tuple of homogeneous polynomials of common degree, not all vanishing on $X$, whose evaluation lands in $Y$ (as a projective point). -/
structure RationalMapTupleRep (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  polys : Fin (n + 1) → MvPolynomial (Fin (m + 1)) k
  deg : ℕ
  polys_homog : ∀ i, (polys i).IsHomogeneous deg
  not_all_vanish : ∃ i, ∃ P ∈ X, eval P.rep (polys i) ≠ 0
  image_in_Y : ∀ P ∈ X,
    (∃ i, eval P.rep (polys i) ≠ 0) →
    ∀ f : MvPolynomial (Fin (n + 1)) k,
    (∀ Q ∈ Y, eval Q.rep f = 0) →
    eval (fun j => eval P.rep (polys j)) f = 0

/-- A tuple representative is defined at $P$ iff at least one coordinate polynomial is nonzero at $P$. -/
def RationalMapTupleRep.isDefinedAt
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : RationalMapTupleRep m n k X Y)
    (P : ℙ k (Fin (m + 1) → k)) : Prop :=
  ∃ i, eval P.rep (φ.polys i) ≠ 0

/-- The vector of values $(\varphi_0(P), \dots, \varphi_n(P))$ of a tuple representative at $P$. -/
noncomputable def RationalMapTupleRep.evalVec
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : RationalMapTupleRep m n k X Y)
    (P : ℙ k (Fin (m + 1) → k)) :
    Fin (n + 1) → k :=
  fun i => eval P.rep (φ.polys i)

/-- Two tuple representatives are equivalent on $X$ iff $\varphi_i \psi_j - \varphi_j \psi_i$ vanishes on $X$ for all $i, j$ (i.e., they define the same projective point at every point of $X$). -/
def RationalMapTupleRep.equivOn
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ ψ : RationalMapTupleRep m n k X Y)
    : Prop :=
  ∀ i j, ∀ P ∈ X,
    eval P.rep (φ.polys i * ψ.polys j - φ.polys j * ψ.polys i) = 0

/-- Cleaner transitivity statement: on a projective variety $X$, `equivOn` is transitive (using primality of the vanishing ideal). -/
structure ProjectiveRationalMap (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  reps : Set (RationalMapTupleRep m n k X Y)
  reps_nonempty : reps.Nonempty
  reps_equiv : ∀ φ₁ ∈ reps, ∀ φ₂ ∈ reps, RationalMapTupleRep.equivOn k φ₁ φ₂
  reps_maximal : ∀ φ, (∃ φ₀ ∈ reps, RationalMapTupleRep.equivOn k φ φ₀) → φ ∈ reps

/-- A projective rational map is regular at $P \in X$ iff some representative is defined at $P$. -/
def ProjectiveRationalMap.IsRegularAt
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y)
    (P : ℙ k (Fin (m + 1) → k))
    (_hP : P ∈ X) : Prop :=
  ∃ rep ∈ φ.reps, rep.isDefinedAt k P

/-- The regular domain of a projective rational map: the locus of points of $X$ where it is regular. -/
def ProjectiveRationalMap.regularDomain
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) :
    Set (ℙ k (Fin (m + 1) → k)) :=
  {P ∈ X | ∃ rep ∈ φ.reps, rep.isDefinedAt k P}


/-- A projective rational map is a morphism iff it is regular at every point of its domain $X$. -/
def ProjectiveRationalMap.IsMorphism
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) : Prop :=
  ∀ (P : ℙ k (Fin (m + 1) → k)) (hP : P ∈ X), φ.IsRegularAt k P hP


/-- A projective morphism $X \to Y$: a projective rational map that is regular everywhere on $X$. -/
structure ProjectiveMorphism (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  toRatMap : ProjectiveRationalMap m n k X Y
  is_morphism : toRatMap.IsMorphism k

/-- The image of a projective rational map $\varphi: X \dashrightarrow Y$: points $Q \in Y$ that arise as $\varphi(P)$ for some $P$ in the regular domain. -/
def ProjectiveRationalMap.image
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  {Q ∈ Y | ∃ P ∈ X, ∃ rep ∈ φ.reps,
    rep.isDefinedAt k P ∧
    ∀ i j, rep.evalVec k P i * Q.rep j = rep.evalVec k P j * Q.rep i}


/-- $S$ is Zariski-dense in $Y$ iff any polynomial vanishing on $S$ also vanishes on $Y$ (i.e., $S$'s Zariski closure contains $Y$). -/
def IsZariskiDenseIn {n : ℕ} (k : Type*) [Field k]
    (S Y : Set (ℙ k (Fin (n + 1) → k))) : Prop :=
  ∀ f : MvPolynomial (Fin (n + 1)) k,
    (∀ Q ∈ S, MvPolynomial.eval Q.rep f = 0) →
    (∀ Q ∈ Y, MvPolynomial.eval Q.rep f = 0)

/-- A projective rational map $\varphi: X \dashrightarrow Y$ is dominant iff its image is Zariski-dense in $Y$. -/
def ProjectiveRationalMap.IsDominant
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) : Prop :=
  IsZariskiDenseIn k (φ.image k) Y

end ProjectiveRatMap

namespace ProjectiveThm1518

open MvPolynomial
open scoped LinearAlgebra.Projectivization
open ProjectiveRegularFunction
open ProjectiveRatMap

variable {m n : ℕ} (k : Type*) [Field k]


/-- Compatibility: for $P \in X$ in the regular domain of $\varphi^* r$, there is a corresponding $Q = \varphi(P) \in Y$ in the regular domain of $r$ such that $(\varphi^* r)(P) = r(Q)$. -/
structure ProjectiveFunctionFieldHom
    (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  toFun : ProjectiveRatFun n k Y → ProjectiveRatFun m k X
  map_eq : ∀ (r₁ r₂ : ProjectiveRatFun n k Y),
    (∀ P ∈ Y, ∀ (hP₁ : P ∈ r₁.regularDomain k) (hP₂ : P ∈ r₂.regularDomain k),
      r₁.evalAt k P hP₁ = r₂.evalAt k P hP₂) →
    toFun r₁ = toFun r₂
  map_mul_eval : ∀ (r₁ r₂ : ProjectiveRatFun n k Y)
    (r₁r₂ : ProjectiveRatFun n k Y),

    (∀ P ∈ Y, ∀ (hP₁ : P ∈ r₁.regularDomain k) (hP₂ : P ∈ r₂.regularDomain k)
      (hP₁₂ : P ∈ r₁r₂.regularDomain k),
      r₁r₂.evalAt k P hP₁₂ = r₁.evalAt k P hP₁ * r₂.evalAt k P hP₂) →
    ∀ P ∈ X,
    ∀ (hPθ₁ : P ∈ (toFun r₁).regularDomain k)
      (hPθ₂ : P ∈ (toFun r₂).regularDomain k)
      (hPθ₁₂ : P ∈ (toFun r₁r₂).regularDomain k),
    (toFun r₁r₂).evalAt k P hPθ₁₂ =
      (toFun r₁).evalAt k P hPθ₁ * (toFun r₂).evalAt k P hPθ₂
  map_add_eval : ∀ (r₁ r₂ : ProjectiveRatFun n k Y)
    (r₁r₂ : ProjectiveRatFun n k Y),

    (∀ P ∈ Y, ∀ (hP₁ : P ∈ r₁.regularDomain k) (hP₂ : P ∈ r₂.regularDomain k)
      (hP₁₂ : P ∈ r₁r₂.regularDomain k),
      r₁r₂.evalAt k P hP₁₂ = r₁.evalAt k P hP₁ + r₂.evalAt k P hP₂) →
    ∀ P ∈ X,
    ∀ (hPθ₁ : P ∈ (toFun r₁).regularDomain k)
      (hPθ₂ : P ∈ (toFun r₂).regularDomain k)
      (hPθ₁₂ : P ∈ (toFun r₁r₂).regularDomain k),
    (toFun r₁r₂).evalAt k P hPθ₁₂ =
      (toFun r₁).evalAt k P hPθ₁ + (toFun r₂).evalAt k P hPθ₂
  map_const_eval : ∀ (c : k) (const_c : ProjectiveRatFun n k Y),

    (∀ P ∈ Y, ∀ (hP : P ∈ const_c.regularDomain k),
      const_c.evalAt k P hP = c) →
    ∀ P ∈ X, ∀ (hP : P ∈ (toFun const_c).regularDomain k),
      (toFun const_c).evalAt k P hP = c

/-- The homogeneous representative for the $i$-th coordinate function $x_i/x_0$ on $\mathbb{P}^n$. -/
noncomputable def coordHomogRep (n : ℕ) (k : Type*) [Field k] (i : Fin (n + 1)) :
    ProjectiveRegularFunction.HomogeneousRep n k where
  num := MvPolynomial.X i
  den := MvPolynomial.X 0
  deg := 1
  num_homog := MvPolynomial.isHomogeneous_X _ _
  den_homog := MvPolynomial.isHomogeneous_X _ _
  den_ne_zero := MvPolynomial.X_ne_zero _

/-- The projective rational function on $Y \subseteq \mathbb{P}^n$ given by the $i$-th coordinate $x_i/x_0$. -/
noncomputable def coordRatFun (n : ℕ) (k : Type*) [Field k]
    (Y : Set (ℙ k (Fin (n + 1) → k)))
    (i : Fin (n + 1)) :
    ProjectiveRatFun n k Y where
  reps := {r : ProjectiveRegularFunction.HomogeneousRep n k |
    r.equivOn k (coordHomogRep n k i) Y}
  reps_nonempty := ⟨coordHomogRep n k i,
    ProjectiveRegularFunction.HomogeneousRep.equivOn_refl k _ _⟩
  reps_equiv := fun r₁ hr₁ r₂ hr₂ => by
    exact ProjectiveRegularFunction.HomogeneousRep.equivOn_trans' r₁
      (coordHomogRep n k i) r₂ hr₁
      (ProjectiveRegularFunction.HomogeneousRep.equivOn_symm k
        r₂ (coordHomogRep n k i) Y hr₂)
  reps_maximal := fun r ⟨r₀, hr₀mem, hrequiv⟩ => by
    exact ProjectiveRegularFunction.HomogeneousRep.equivOn_trans' r r₀
      (coordHomogRep n k i) hrequiv hr₀mem

/-- The chosen homogeneous representative of $\theta(x_i/x_0) \in k(X)$ given a function-field homomorphism $\theta: k(Y) \to k(X)$. -/
noncomputable def inducedCoordRep
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (θ : ProjectiveFunctionFieldHom m n k X Y)
    (i : Fin (n + 1)) :
    ProjectiveRegularFunction.HomogeneousRep m k :=
  (θ.toFun (coordRatFun n k Y i)).reps_nonempty.choose

/-- The common degree shared by all the induced polynomials: the sum of the degrees of the coordinate representatives. Used to put all $\theta(x_i/x_0)$ on a common denominator. -/
noncomputable def inducedCommonDeg
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (θ : ProjectiveFunctionFieldHom m n k X Y) :
    ℕ :=
  ∑ j : Fin (n + 1), (inducedCoordRep k θ j).deg

/-- The $i$-th coordinate polynomial of the projective map induced by $\theta$: the $i$-th numerator times the product of all other denominators (clearing denominators to common degree). -/
noncomputable def inducedPoly
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (θ : ProjectiveFunctionFieldHom m n k X Y)
    (i : Fin (n + 1)) :
    MvPolynomial (Fin (m + 1)) k :=
  (inducedCoordRep k θ i).num *
    ∏ j ∈ Finset.univ.erase i, (inducedCoordRep k θ j).den
