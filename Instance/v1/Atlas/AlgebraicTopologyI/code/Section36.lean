/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Algebra.Group.Subgroup.Ker
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section36
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The reverse-inclusion preorder on `OpenNbhdPair K L`: a pair `p` is smaller
than `q` when `q.U ⊆ p.U` and `q.V ⊆ p.V`. This makes the family of pairs into
a directed system as the neighbourhoods shrink down to `(K, L)`. -/
instance openNbhdPair_preorder {X : Type} [TopologicalSpace X] {K L : Set X} :
    Preorder (OpenNbhdPair K L) where
  le p q := q.U ≤ p.U ∧ q.V ≤ p.V
  le_refl p := ⟨le_refl _, le_refl _⟩
  le_trans p q r hpq hqr := ⟨le_trans hqr.1 hpq.1, le_trans hqr.2 hpq.2⟩

end FullyRelativeCapProduct
end
