/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Morphisms
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Morphisms
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.MvPolynomial.Basic

variable (k : Type*) [Field k]

/-- Embedding $\overline{k}[x_1, \ldots, x_m] \hookrightarrow \overline{k}[x_1, \ldots, x_{m+n}]$
in the first $m$ variables, by renaming via `Fin.castAdd`. -/
noncomputable def embedPolyLeft (m n : ℕ) :
    MvPolynomial (Fin m) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.castAdd n)

/-- Embedding $\overline{k}[y_1, \ldots, y_n] \hookrightarrow \overline{k}[x_1, \ldots, x_{m+n}]$
in the last $n$ variables, by renaming via `Fin.natAdd`. -/
noncomputable def embedPolyRight (m n : ℕ) :
    MvPolynomial (Fin n) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.natAdd m)

/-- Image of a set of polynomials under `embedPolyLeft`. -/
def embedSetLeft (m n : ℕ) (S : Set (MvPolynomial (Fin m) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + n)) (AlgebraicClosure k)) :=
  (embedPolyLeft k m n) '' S

/-- Image of a set of polynomials under `embedPolyRight`. -/
def embedSetRight (m n : ℕ) (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + n)) (AlgebraicClosure k)) :=
  (embedPolyRight k m n) '' S

/-- Definition 16.2: the product algebraic set $V(S_X) \times V(S_Y) \subseteq \overline{k}^{m+n}$,
defined as the algebraic set in $\overline{k}^{m+n}$ cut out by the embedded polynomials. -/
def ProductAlgebraicSet (m n : ℕ)
    (S_X : Set (MvPolynomial (Fin m) (AlgebraicClosure k)))
    (S_Y : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    Set (AffineSpace_k k (m + n)) :=
  AlgebraicSet k (m + n) (embedSetLeft k m n S_X ∪ embedSetRight k m n S_Y)

/-- Projection $\overline{k}^{m+n} \to \overline{k}^m$ onto the first $m$ coordinates. -/
def projLeft (m n : ℕ) (P : AffineSpace_k k (m + n)) : AffineSpace_k k m :=
  P ∘ Fin.castAdd n

/-- Projection $\overline{k}^{m+n} \to \overline{k}^n$ onto the last $n$ coordinates. -/
def projRight (m n : ℕ) (P : AffineSpace_k k (m + n)) : AffineSpace_k k n :=
  P ∘ Fin.natAdd m

/-- The Cartesian product $X \times Y \subseteq \overline{k}^{m+n}$ as a set, defined by the
projection criteria. -/
def CartesianProduct (m n : ℕ)
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) :
    Set (AffineSpace_k k (m + n)) :=
  {P | projLeft k m n P ∈ X ∧ projRight k m n P ∈ Y}

/-- Partial evaluation of a polynomial in $m+n$ variables by fixing the last $n$ variables to
the values $b \in \overline{k}^n$, returning a polynomial in the first $m$ variables. -/
noncomputable def partialEvalRight (m n : ℕ) (b : AffineSpace_k k n) :
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) →+*
    MvPolynomial (Fin m) (AlgebraicClosure k) :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin (m + n) =>
      if h : i.val < m
      then MvPolynomial.X ⟨i.val, h⟩
      else MvPolynomial.C (b ⟨i.val - m, by omega⟩))

/-- Partial evaluation of a polynomial in $m+n$ variables by fixing the first $m$ variables
to the values $a \in \overline{k}^m$, returning a polynomial in the last $n$ variables. -/
noncomputable def partialEvalLeft (m n : ℕ) (a : AffineSpace_k k m) :
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) →+*
    MvPolynomial (Fin n) (AlgebraicClosure k) :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin (m + n) =>
      if h : i.val < m
      then MvPolynomial.C (a ⟨i.val, h⟩)
      else MvPolynomial.X ⟨i.val - m, by omega⟩)

/-- The $\overline{k}$-vanishing ideal of a subset $V \subseteq \overline{k}^n$: polynomials
in $\overline{k}[x_1, \ldots, x_n]$ that vanish on $V$. -/
def vanishingIdeal_kbar (n : ℕ) (V : Set (AffineSpace_k k n)) :
    Ideal (MvPolynomial (Fin n) (AlgebraicClosure k)) where
  carrier := {f | ∀ P ∈ V, MvPolynomial.eval P f = 0}
  add_mem' := by
    intro a b ha hb P hP
    simp [ha P hP, hb P hP]
  zero_mem' := by intro P _; simp
  smul_mem' := by intro c f hf P hP; simp [hf P hP]

/-- If $P \in V$, then every polynomial vanishing on $V$ vanishes at $P$, i.e.
$I(V) \subseteq \ker(\mathrm{eval}_P)$. -/
lemma idealOfAlgebraicSet_le_ker_eval
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    idealOfAlgebraicSet V ≤ RingHom.ker (MvPolynomial.eval P) := by
  intro f hf
  rw [RingHom.mem_ker]
  exact hf P hP

/-- Evaluation at a point $P \in V$ descends to a ring homomorphism
$\overline{k}[V] \to \overline{k}$ from the coordinate ring. -/
noncomputable def evalOnCoordinateRingBar
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    AffineCoordinateRingBar V →+* AlgebraicClosure k :=
  Ideal.Quotient.lift (idealOfAlgebraicSet V) (MvPolynomial.eval P)
    (idealOfAlgebraicSet_le_ker_eval V P hP)

/-- The maximal ideal $\mathfrak{m}_P \subseteq \overline{k}[V]$ associated to a point
$P \in V$, defined as the kernel of evaluation at $P$. -/
noncomputable def maximalIdealOfPoint
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    Ideal (AffineCoordinateRingBar V) :=
  RingHom.ker (evalOnCoordinateRingBar V P hP)

/-- The product projective space $\mathbb{P}^m \times \mathbb{P}^n$ over $k$ as a Cartesian
product of projective spaces. -/
def ProductProjectiveSpace (k : Type*) [Field k] (m n : ℕ) : Type _ :=
  ProjectiveSpace_k k m × ProjectiveSpace_k k n

/-- A *bihomogeneous polynomial* of bi-degree $(d_X, d_Y)$: a polynomial in
$m + 1 + (n + 1)$ variables which is homogeneous of degree $d_X$ in the first $m + 1$
variables and homogeneous of degree $d_Y$ in the last $n + 1$ variables. -/
structure BihomogPoly (k : Type*) [Field k] (m n : ℕ) where
  poly : MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)
  degX : ℕ
  degY : ℕ
  homogX : ∀ (c : AlgebraicClosure k) (v : Fin (m + 1 + (n + 1)) → AlgebraicClosure k),
    eval (fun i => if i.val < m + 1 then c * v i else v i) poly =
    c ^ degX * eval v poly
  homogY : ∀ (c : AlgebraicClosure k) (v : Fin (m + 1 + (n + 1)) → AlgebraicClosure k),
    eval (fun i => if i.val < m + 1 then v i else c * v i) poly =
    c ^ degY * eval v poly

/-- Embedding $\overline{k}[x_0, \ldots, x_m] \hookrightarrow$ the bigger polynomial ring in
$m + 1 + (n + 1)$ variables, on the first $m + 1$ variables. -/
noncomputable def embedHomogPolyLeft {k : Type*} [Field k] (m n : ℕ) :
    MvPolynomial (Fin (m + 1)) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.castAdd (n + 1))

/-- Embedding $\overline{k}[y_0, \ldots, y_n] \hookrightarrow$ the bigger polynomial ring in
$m + 1 + (n + 1)$ variables, on the last $n + 1$ variables. -/
noncomputable def embedHomogPolyRight {k : Type*} [Field k] (m n : ℕ) :
    MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.natAdd (m + 1))

/-- Image of a set of homogeneous polynomials under `embedHomogPolyLeft`. -/
def embedHomogSetLeft {k : Type*} [Field k] (m n : ℕ)
    (S : Set (MvPolynomial (Fin (m + 1)) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)) :=
  (embedHomogPolyLeft m n) '' S

/-- Image of a set of homogeneous polynomials under `embedHomogPolyRight`. -/
def embedHomogSetRight {k : Type*} [Field k] (m n : ℕ)
    (S : Set (MvPolynomial (Fin (n + 1)) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)) :=
  (embedHomogPolyRight m n) '' S

/-- Evaluating $\mathrm{embedHomogPolyLeft}(p)$ at `Fin.append a b` equals evaluating $p$
at $a$. -/
theorem eval_embedHomogPolyLeft {k : Type*} [Field k] (m n : ℕ)
    (p : MvPolynomial (Fin (m + 1)) (AlgebraicClosure k))
    (a : Fin (m + 1) → AlgebraicClosure k) (b : Fin (n + 1) → AlgebraicClosure k) :
    eval (Fin.append a b) (embedHomogPolyLeft m n p) = eval a p := by
  simp only [embedHomogPolyLeft, eval_rename]
  have : Fin.append a b ∘ Fin.castAdd (n + 1) = a := by
    funext i; exact Fin.append_left a b i
  rw [this]

/-- Evaluating $\mathrm{embedHomogPolyRight}(p)$ at `Fin.append a b` equals evaluating $p$
at $b$. -/
theorem eval_embedHomogPolyRight {k : Type*} [Field k] (m n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k))
    (a : Fin (m + 1) → AlgebraicClosure k) (b : Fin (n + 1) → AlgebraicClosure k) :
    eval (Fin.append a b) (embedHomogPolyRight m n p) = eval b p := by
  simp only [embedHomogPolyRight, eval_rename]
  have : Fin.append a b ∘ Fin.natAdd (m + 1) = b := by
    funext i; exact Fin.append_right a b i
  rw [this]

/-- The combined polynomial set: union of the embeddings of homogeneous polynomial sets from
$\mathbb{P}^m$ and $\mathbb{P}^n$ into the bigger polynomial ring. -/
def combinedHomogPolySet {k : Type*} [Field k] (m n : ℕ)
    (S_X : Set (HomogPoly k m))
    (S_Y : Set (HomogPoly k n)) :
    Set (MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)) :=
  embedHomogSetLeft m n (HomogPoly.poly '' S_X) ∪
  embedHomogSetRight m n (HomogPoly.poly '' S_Y)

/-- Vanishing of the combined homogeneous polynomial set is invariant under rescaling each
of the two homogeneous coordinate vectors by a nonzero scalar (well-definedness on
projective coordinates). -/
lemma combinedHomogPolySet_vanish_of_rescale {k : Type*} [Field k] {m n : ℕ}
    {S_X : Set (HomogPoly k m)} {S_Y : Set (HomogPoly k n)}
    {a₁ : Fin (m + 1) → AlgebraicClosure k} {b₁ : Fin (n + 1) → AlgebraicClosure k}
    {a₂ : Fin (m + 1) → AlgebraicClosure k} {b₂ : Fin (n + 1) → AlgebraicClosure k}
    {c d : AlgebraicClosure k} (hc : c ≠ 0) (hd : d ≠ 0)
    (ha : a₁ = fun i => c * a₂ i) (hb : b₁ = fun i => d * b₂ i)
    (h : ∀ f ∈ combinedHomogPolySet m n S_X S_Y, eval (Fin.append a₁ b₁) f = 0) :
    ∀ f ∈ combinedHomogPolySet m n S_X S_Y, eval (Fin.append a₂ b₂) f = 0 := by
  intro f hf
  simp only [combinedHomogPolySet, Set.mem_union, embedHomogSetLeft, embedHomogSetRight,
    Set.mem_image] at hf
  rcases hf with ⟨p, ⟨g, hgS, rfl⟩, rfl⟩ | ⟨q, ⟨g, hgS, rfl⟩, rfl⟩
  · have hmem : (embedHomogPolyLeft m n) g.poly ∈ combinedHomogPolySet m n S_X S_Y :=
      Set.mem_union_left _ ⟨g.poly, ⟨g, hgS, rfl⟩, rfl⟩
    have heval := h _ hmem
    rw [eval_embedHomogPolyLeft] at heval ⊢
    rw [ha, homog_eval_rescale] at heval
    exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hc)
  · have hmem : (embedHomogPolyRight m n) g.poly ∈ combinedHomogPolySet m n S_X S_Y :=
      Set.mem_union_right _ ⟨g.poly, ⟨g, hgS, rfl⟩, rfl⟩
    have heval := h _ hmem
    rw [eval_embedHomogPolyRight] at heval ⊢
    rw [hb, homog_eval_rescale] at heval
    exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hd)

/-- The product projective algebraic set in $\mathbb{P}^m \times \mathbb{P}^n$ cut out by
two sets of homogeneous polynomials, defined as the common zero locus of the combined set
on the quotient $\mathbb{P}^m \times \mathbb{P}^n$. -/
def ProductProjectiveAlgebraicSet {k : Type*} [Field k] (m n : ℕ)
    (S_X : Set (HomogPoly k m))
    (S_Y : Set (HomogPoly k n)) :
    Set (ProductProjectiveSpace k m n) :=
  {PQ | Quotient.liftOn₂ PQ.1 PQ.2
    (fun v w => ∀ f ∈ combinedHomogPolySet m n S_X S_Y,
      eval (Fin.append v.1 w.1) f = 0)
    (by
      intro a₁ b₁ a₂ b₂ ⟨c, hc, hab1⟩ ⟨d, hd, hab2⟩
      simp only [eq_iff_iff]
      constructor
      · exact combinedHomogPolySet_vanish_of_rescale hc hd
          (funext (hab1 ·)) (funext (hab2 ·))
      · exact combinedHomogPolySet_vanish_of_rescale
          (inv_ne_zero hc) (inv_ne_zero hd)
          (funext fun i => by rw [hab1 i, inv_mul_cancel_left₀ hc])
          (funext fun i => by rw [hab2 i, inv_mul_cancel_left₀ hd]))}

/-- A subset $V \subseteq \mathbb{P}^m \times \mathbb{P}^n$ is a product projective algebraic
set if it equals `ProductProjectiveAlgebraicSet S_X S_Y` for some homogeneous polynomial sets. -/
def IsProductProjectiveAlgSet {k : Type*} [Field k] (m n : ℕ)
    (V : Set (ProductProjectiveSpace k m n)) : Prop :=
  ∃ (S_X : Set (HomogPoly k m)) (S_Y : Set (HomogPoly k n)),
    V = ProductProjectiveAlgebraicSet m n S_X S_Y


/-- Concatenation of two vectors of homogeneous coordinates from $\mathbb{A}^{m+1}$ and
$\mathbb{A}^{n+1}$ into a single vector in $\mathbb{A}^{m+1+(n+1)}$. -/
def concatVec {k : Type*} [Field k] (m n : ℕ) (a : Fin (m + 1) → AlgebraicClosure k)
    (b : Fin (n + 1) → AlgebraicClosure k) :
    Fin (m + 1 + (n + 1)) → AlgebraicClosure k :=
  Fin.append a b

/-- The Segre map on coordinates: $((a_i), (b_j)) \mapsto (a_i b_j)_{i,j}$, sending
$\mathbb{A}^{m+1} \times \mathbb{A}^{n+1} \to \mathbb{A}^{(m+1)(n+1)}$, indexed by
the pair $(i, j)$ encoded as $i \cdot (n+1) + j$. -/
noncomputable def segreMap {k : Type*} [Field k] (m n : ℕ)
    (a : Fin (m + 1) → AlgebraicClosure k)
    (b : Fin (n + 1) → AlgebraicClosure k) :
    Fin ((m + 1) * (n + 1)) → AlgebraicClosure k :=
  fun ij => a (Fin.mk (ij.val / (n + 1))
              (Nat.div_lt_of_lt_mul (Nat.mul_comm (m+1) (n+1) ▸ ij.isLt))) *
            b (Fin.mk (ij.val % (n + 1)) (Nat.mod_lt _ (by omega)))
