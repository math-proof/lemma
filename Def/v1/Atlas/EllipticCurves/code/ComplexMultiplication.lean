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


namespace ComplexLattice

noncomputable section

open Pointwise

/-- The *endomorphism ring* $\mathrm{End}(L)$ of a complex lattice $L$ is the subring
of $\mathbb{C}$ consisting of all $\alpha \in \mathbb{C}$ such that $\alpha L \subseteq L$.
Equivalently, an element $\alpha$ lies in $\mathrm{End}(L)$ iff multiplication by $\alpha$
preserves the additive subgroup underlying $L$. -/
def endomorphismRing (L : ComplexLattice) : Subring ℂ where
  carrier := { α : ℂ | ∀ z ∈ L.toAddSubgroup, α * z ∈ L.toAddSubgroup }
  mul_mem' {a b} ha hb z hz := by rw [mul_assoc]; exact ha _ (hb z hz)
  one_mem' z hz := by rwa [one_mul]
  add_mem' {a b} ha hb z hz := by
    rw [add_mul]; exact L.toAddSubgroup.add_mem (ha z hz) (hb z hz)
  zero_mem' _ _ := by rw [zero_mul]; exact L.toAddSubgroup.zero_mem
  neg_mem' {a} ha z hz := by rw [neg_mul]; exact L.toAddSubgroup.neg_mem (ha z hz)

end
end ComplexLattice
