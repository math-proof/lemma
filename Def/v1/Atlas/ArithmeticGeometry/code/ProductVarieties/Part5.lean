/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Morphisms
import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part6
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.ProductVarieties.Part3
variable (k : Type*) [Field k]


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

