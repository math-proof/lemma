/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section23.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.Order.Directed
import Mathlib.Algebra.Colimit.Module
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.Flat.Localization
import Def.v1.Atlas.AlgebraicTopologyI.code.Section23


namespace DirectedSystems

/-- Definition 23.2. A poset `(I, ≤)` is directed if for every `i, j ∈ I` there is some
`k ∈ I` with `i ≤ k` and `j ≤ k`. -/
abbrev DirectedPoset (I : Type*) [Preorder I] : Prop :=
  IsDirected I (· ≤ ·)

open CategoryTheory

/-- Definition 23.4. An `I`-directed system in a category `C` (for `I` a directed poset)
is a functor `I ⥤ C`, i.e. objects `X_i` together with coherent maps `X_i → X_j` whenever
`i ≤ j`. -/
abbrev DirectedSystemFunctor (I : Type*) [Preorder I] [IsDirected I (· ≤ ·)]
    (C : Type*) [Category C] :=
  Functor I C

section CategoricalDirectLimit

open CategoryTheory CategoryTheory.Limits

/-- Definition 23.8 (categorical form). The direct limit `lim→ F` of a diagram `F : J ⥤ C`
is the colimit of `F`, i.e. the initial cocone under `F`. -/
noncomputable abbrev CategoricalDirectLimit {J : Type*} [Category J] {C : Type*} [Category C]
    (F : J ⥤ C) [HasColimit F] : C :=
  colimit F

end CategoricalDirectLimit

/-- Definition 23.8 (module form). The direct limit of a directed system of `R`-modules,
realized as Mathlib's `Module.DirectLimit` of the modules `G i` along the structure maps `f`. -/
abbrev DirectLimit
    (R : Type*) [Semiring R]
    (ι : Type*) [Preorder ι] [DecidableEq ι]
    (G : ι → Type*) [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) : Type _ :=
  Module.DirectLimit G f

end DirectedSystems
