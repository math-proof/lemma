/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part6
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RiemannRoch
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Finsupp
open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily


/-- Structure capturing the residue-field surjection at each place. For each
place $p \in P$, `degPlace p` is the $k$-degree of the residue field
$\mathcal{O}_p / \mathfrak{m}_p$, and `φ D p₀` is a surjective $k$-linear map
from $A(D+p_0)$ onto $\mathcal{O}_{p_0}/\mathfrak{m}_{p_0}$ whose kernel is
exactly $A(D)$ — packaging the ingredient needed for Lemma 22.8. -/
class HasResidueFieldSurjection (P : Type*) (F : Type*) (k : Type*)
    [DecidableEq P] [Field k] [Field F] [Algebra k F]
    (O : P → ValuationSubring F)
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k] where
  degPlace : P → ℕ
  degPlace_pos : ∀ p, 0 < degPlace p
  φ : ∀ (D : P → ℤ) (p₀ : P),
    ↥(adeleSpace (F := F) (O := O) k (Function.update D p₀ (D p₀ + 1))) →ₗ[k]
    (Fin (degPlace p₀) → k)
  φ_surj : ∀ (D : P → ℤ) (p₀ : P), Function.Surjective (φ D p₀)
  φ_ker : ∀ (D : P → ℤ) (p₀ : P),
    LinearMap.ker (φ D p₀) =
      Submodule.comap
        (adeleSpace (F := F) (O := O) k (Function.update D p₀ (D p₀ + 1))).subtype
        (adeleSpace (F := F) (O := O) k D)

