/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Flat.CategoryTheory
import Def.v1.Atlas.AlgebraicTopologyI.code.Section24.Part3
open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace UniversalCoefficientTheorem

/-- Packaged data of the **Universal Coefficient Theorem** in degree $n+1$: for every
free chain complex $C_*$ over a PID $R$ and every $R$-module $M$, a natural split short
exact sequence
$$0 \to H_{n+1}(C_*) \otimes M \xrightarrow{\alpha} H_{n+1}(C_* \otimes M) \xrightarrow{\beta} \operatorname{Tor}_1^R(H_n(C_*), M) \to 0,$$
together with naturality of $\alpha$ and $\beta$ in $C_*$. -/
structure NaturalUCTData (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ) where
  α : (C : ChainComplex (ModuleCat R) ℕ) → (∀ i, Module.Free R (C.X i)) →
    (C.homology (n + 1) ⊗ M ⟶ (tensorComplex R C M).homology (n + 1))
  β : (C : ChainComplex (ModuleCat R) ℕ) → (∀ i, Module.Free R (C.X i)) →
    ((tensorComplex R C M).homology (n + 1) ⟶ ((Tor (ModuleCat R) 1).obj (C.homology n)).obj M)
  zero : ∀ (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)),
    α C hfree ≫ β C hfree = 0
  shortExact : ∀ (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)),
    (ShortComplex.mk (α C hfree) (β C hfree) (zero C hfree)).ShortExact
  splitting : ∀ (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)),
    Nonempty (ShortComplex.mk (α C hfree) (β C hfree) (zero C hfree)).Splitting
  α_natural : ∀ (C D : ChainComplex (ModuleCat R) ℕ)
    (hfreeC : ∀ i, Module.Free R (C.X i)) (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D),
    α C hfreeC ≫ HomologicalComplex.homologyMap (tensorComplexMap R φ M) (n + 1) =
      ((tensoringRight (ModuleCat R)).obj M).map (HomologicalComplex.homologyMap φ (n + 1)) ≫
        α D hfreeD
  β_natural : ∀ (C D : ChainComplex (ModuleCat R) ℕ)
    (hfreeC : ∀ i, Module.Free R (C.X i)) (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D),
    β C hfreeC ≫ ((Tor (ModuleCat R) 1).map (HomologicalComplex.homologyMap φ n)).app M =
      HomologicalComplex.homologyMap (tensorComplexMap R φ M) (n + 1) ≫ β D hfreeD

end UniversalCoefficientTheorem
end
