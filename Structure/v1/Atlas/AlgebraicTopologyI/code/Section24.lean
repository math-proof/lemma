/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section24.Part3
open CategoryTheory MonoidalCategory Limits


public noncomputable section

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
