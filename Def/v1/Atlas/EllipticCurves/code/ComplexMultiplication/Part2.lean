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
import Theorem.v1.Atlas.EllipticCurves.code.ComplexMultiplication


namespace ComplexLattice

noncomputable section

open Pointwise

/-- A complex lattice $L$ is a *proper $\mathcal{O}$-ideal* if its endomorphism ring
equals $\mathcal{O}$ exactly (not just contains $\mathcal{O}$).  This is the standard
notion of proper ideal in the theory of orders in imaginary quadratic fields. -/
def IsProperIdeal (𝒪 : Subring ℂ) (L : ComplexLattice) : Prop :=
  L.endomorphismRing = 𝒪

/-- Two proper $\mathcal{O}$-ideals $L_1$ and $L_2$ are *equivalent* if there exist
nonzero $\alpha, \beta \in \mathcal{O}$ with $\alpha L_1 = \beta L_2$ as subsets of
$\mathbb{C}$.  This is the equivalence relation whose classes form the ideal class
group of $\mathcal{O}$. -/
def IsEquivalent (𝒪 : Subring ℂ) (L₁ L₂ : ComplexLattice) : Prop :=
  ∃ (α β : 𝒪), (α : ℂ) ≠ 0 ∧ (β : ℂ) ≠ 0 ∧
    (α : ℂ) • (L₁.lattice : Set ℂ) = (β : ℂ) • (L₂.lattice : Set ℂ)

end
end ComplexLattice
