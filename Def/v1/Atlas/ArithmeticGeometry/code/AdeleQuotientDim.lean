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
import Instance.v1.Atlas.ArithmeticGeometry.code.AdeleQuotientDim
open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily


/-- The *degree* $\deg p = [\mathcal{O}_p / \mathfrak{m}_p : k]$ of a place
$p$, defined as the $k$-dimension of the residue field. -/
noncomputable def placeDegree {P : Type*} {F : Type*} {k : Type*}
    [DecidableEq P] [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k] : P → ℕ := fun p =>
  Module.finrank k (IsLocalRing.ResidueField ↥(O p))

/-- $k$-linear projection of an adele onto its $p_0$-component: the map
$\alpha \mapsto \alpha(p_0)$ from the adele ring to $F$. -/
noncomputable def adeleComponentMap {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)]
    (p₀ : P) : FunctionFieldAdeleRing F P O →ₗ[k] F where
  toFun α := α p₀
  map_add' α β := by
    show (α + β) p₀ = α p₀ + β p₀
    rfl
  map_smul' c α := by
    show (c • α) p₀ = c • (α p₀)
    rw [FunctionFieldAdeleRing.smul_apply]
    simp only [Algebra.smul_def]

/-- The composed surjection
$A(D + p_0) \xrightarrow{\alpha \mapsto \alpha(p_0)} F \xrightarrow{\varphi}
k^{\deg p_0}$ realizing the residue-field surjection at the place $p_0$. -/
noncomputable def adeleDivisorDeg {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [DiscreteValuationFamily P F k]
    [DecidableEq P] [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [HasResidueFieldSurjection P F k O] (D : P →₀ ℤ) : ℤ :=
  D.sum (fun p n => n * (HasResidueFieldSurjection.degPlace (F := F) (k := k) (O := O) p : ℤ))

