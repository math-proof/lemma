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
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part5


namespace ComplexLattice

noncomputable section

/-- Zero belongs to the *lattice multiplier set* $\{\alpha \in \mathbb{C} : \alpha L_1
\subseteq L_2\}$. -/
theorem latticeMulSet_zero_mem (L₁ L₂ : ComplexLattice) :
    (0 : ℂ) ∈ latticeMulSet L₁ L₂ :=
  zero_mem_latticeMulSet L₁ L₂

/-- The lattice multiplier set is closed under addition: if $\alpha L_1, \beta L_1
\subseteq L_2$, then $(\alpha + \beta) L_1 \subseteq L_2$. -/
theorem latticeMulSet_add_mem (L₁ L₂ : ComplexLattice) {α β : ℂ}
    (hα : α ∈ latticeMulSet L₁ L₂) (hβ : β ∈ latticeMulSet L₁ L₂) :
    α + β ∈ latticeMulSet L₁ L₂ := by
  intro z hz
  rw [add_mul]
  exact L₂.lattice.add_mem (hα z hz) (hβ z hz)

/-- The lattice multiplier set is closed under negation: if $\alpha L_1 \subseteq L_2$,
then $-\alpha \cdot L_1 \subseteq L_2$. -/
theorem latticeMulSet_neg_mem (L₁ L₂ : ComplexLattice) {α : ℂ}
    (hα : α ∈ latticeMulSet L₁ L₂) :
    -α ∈ latticeMulSet L₁ L₂ := by
  intro z hz
  rw [neg_mul]
  exact L₂.lattice.neg_mem (hα z hz)

end
end ComplexLattice
