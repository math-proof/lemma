/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO

namespace DVRContext

variable (C : DVRContext)


/-- *Anisotropic quadratic space data*: a symmetric bilinear form on $V = k^n$ that is
anisotropic ($B(v,v) = 0 \Rightarrow v = 0$), together with the auxiliary hypotheses needed
to construct the unique maximal $\mathfrak{o}$-valued lattice: $2$ is a unit in
$\mathfrak{o}$, the uniformizer's image is nonzero, $\mathfrak{o}$ is integrally closed for
squares ($a^2 \in \mathfrak{o} \Rightarrow a \in \mathfrak{o}$), $\mathfrak{o}$ is
Henselian, and a normalisation hypothesis controlling the valuation of cross-ratios
$B(x,y)/B(x,x)$. -/
structure AnisotropicQuadSpace where
  form : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k
  form_symm : ∀ v w, form v w = form w v
  form_smul_left : ∀ (r : C.k) v w, form (r • v) w = r * form v w
  form_add_left : ∀ u v w, form (u + v) w = form u w + form v w
  anisotropic : ∀ v, form v v = 0 → v = 0
  two_unit : C.isUnitInO (2 : C.k)
  embed_pi_ne_zero : C.embed C.uniformizer ≠ 0
  dvr_sq_integral : ∀ a : C.k, C.isInO (a * a) → C.isInO a
  inst_henselian : HenselianLocalRing C.𝔬
  hmax : C.maxIdeal = @IsLocalRing.maximalIdeal C.𝔬 C.inst_comm_ring.toCommSemiring
    inst_henselian.toIsLocalRing
  dvr_normalize_ratio : ∀ (a d : C.k),
    ¬C.isInO a → C.isInO d → d ≠ 0 →
    ∃ (n : ℕ), 0 < n ∧
      C.isUnitInO (C.embed C.uniformizer ^ n * (a * d⁻¹)) ∧
      ∀ (e : C.k), C.isInO e →
        C.isInMaxIdeal (C.embed C.uniformizer ^ (2 * n) * (e * d⁻¹))

namespace AnisotropicQuadSpace

variable {C} (B : AnisotropicQuadSpace C)


/-- *The maximal $\mathfrak{o}$-integral set*: vectors $v \in V$ such that $B(v, v) \in
\mathfrak{o}$. This is shown below to be the carrier of the unique maximal
$\mathfrak{o}$-valued lattice. -/
def integralCarrier : Set (Fin C.n → C.k) :=
  { v | C.isInO (B.form v v) }

/-- *$\mathfrak{o}$-valued lattice*: a lattice $\Lambda$ is $\mathfrak{o}$-valued if the form
$B$ takes values in $\mathfrak{o}$ on $\Lambda \times \Lambda$. -/
def IsOValued (Λ : C.OLattice) : Prop :=
  ∀ v w, v ∈ Λ.carrier → w ∈ Λ.carrier → C.isInO (B.form v w)
