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
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part4


namespace ComplexLattice

noncomputable section

/-- *Classification of endomorphism rings* (Theorem 12.17): the endomorphism ring
of any complex lattice $L$ is either isomorphic to $\mathbb{Z}$ (constructor `isZ`),
or is an order in an imaginary quadratic field (constructor `isOrderInImagQuadField`),
in which case $L$ embeds into that order via $\alpha \mapsto \alpha\omega_1$. -/
inductive EndomorphismRingClassification (L : ComplexLattice) : Prop where
  | isZ (h : ∀ α : ℂ, α ∈ L.endomorphismRing → ∃ n : ℤ, α = (n : ℂ)) :
      EndomorphismRingClassification L
  | isOrderInImagQuadField
      (hIsOrder : IsImagQuadOrder L.endomorphismRing)
      (hLatticeEmbed : ∀ α : ℂ, α ∈ L.endomorphismRing →
        ∃ a' b' : ℤ, ↑a' * L.ω₁ + ↑b' * L.ω₂ = α * L.ω₁) :
      EndomorphismRingClassification L

end
end ComplexLattice
