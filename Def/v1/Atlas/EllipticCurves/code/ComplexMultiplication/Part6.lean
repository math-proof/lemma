/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.EllipticFunction.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EllipticFunction
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Theorem161
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Structure.v1.Atlas.EllipticCurves.code.Theorem161
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Theorem.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part4


namespace ComplexLattice

noncomputable section

/-- The lattice multiplier set $\{\alpha : \alpha L_1 \subseteq L_2\}$ packaged as an
additive subgroup of $\mathbb{C}$. -/
def latticeMulAddSubgroup (L₁ L₂ : ComplexLattice) : AddSubgroup ℂ where
  carrier := latticeMulSet L₁ L₂
  zero_mem' := latticeMulSet_zero_mem L₁ L₂
  add_mem' := latticeMulSet_add_mem L₁ L₂
  neg_mem' := latticeMulSet_neg_mem L₁ L₂

/-- A function $f : \mathbb{C} \to \mathbb{C}$ is *even* iff $f(-z) = f(z)$ for all
$z$. -/
def IsEvenFunction (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, f (-z) = f z

variable (L : ComplexLattice)

/-- $\wp_{L_2}(\alpha z)$ is a *rational function in $\wp_{L_1}(z)$*: there exist
polynomials $u, v$ with $v \neq 0$ such that $v(\wp_{L_1}(z)) \wp_{L_2}(\alpha z) =
u(\wp_{L_1}(z))$.  Condition (2) of Theorem 16.4. -/
def IsRationalFunctionInWP (L₁ L₂ : ComplexLattice) (α : ℂ) : Prop :=
  ∃ (u v : ℂ[X]), v ≠ 0 ∧
    ∀ z : ℂ, v.eval (L₁.weierstrassP z) * L₂.weierstrassP (α * z) =
      u.eval (L₁.weierstrassP z)

/-- The "isogeny" associated to $\alpha$ exists at the level of $\wp$-functions
and their derivatives: both $\wp_{L_2}(\alpha z)$ and $\wp'_{L_2}(\alpha z)$ can
be expressed rationally in $\wp_{L_1}$ and $\wp'_{L_1}$.  Condition (3) of
Theorem 16.4. -/
def ExistsUniqueIsogenyFromAlpha (L₁ L₂ : ComplexLattice) (α : ℂ) : Prop :=
  ∃ (u v s t : ℂ[X]), v ≠ 0 ∧ t ≠ 0 ∧
    (∀ z : ℂ, v.eval (L₁.weierstrassP z) * L₂.weierstrassP (α * z) =
      u.eval (L₁.weierstrassP z)) ∧
    (∀ z : ℂ, t.eval (L₁.weierstrassP z) * L₂.derivWeierstrassP (α * z) =
      s.eval (L₁.weierstrassP z) * L₁.derivWeierstrassP z)

end
end ComplexLattice
