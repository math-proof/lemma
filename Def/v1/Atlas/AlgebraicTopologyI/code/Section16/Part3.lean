/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.Category.Grp.Abelian
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section16
open AlgebraicTopology CategoryTheory Limits AlgebraicTopologyI


noncomputable section

namespace CWComplex.SkeletonHomology

namespace CWHomology

/-- The restriction of a cellular map `f : X → Y` to the `n`-skeletons, viewed as a
morphism `X_n ⟶ Y_n` in `TopCat`. -/
def cellularMapOnSkeleton
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    TopCat.of ↥(CWComplex.skeleton X (n : ℕ∞) : Set X) ⟶
    TopCat.of ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y) :=
  TopCat.ofHom ⟨fun ⟨x, hx⟩ => ⟨f x, hf.mapsTo_skeleton n hx⟩,
    Continuous.subtype_mk (f.continuous.comp continuous_subtype_val) _⟩

/-- The restriction of a cellular map `f` to the previous-skeleton subspace, viewed as a
morphism between the preimages of `X_{n-1}` (in `X_n`) and `Y_{n-1}` (in `Y_n`). -/
def cellularMapOnPrevSkeleton
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X) :
      Set ↥(CWComplex.skeleton X (n : ℕ∞) : Set X)) ⟶
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton Y ((↑(n - 1) : ℕ∞)) : Set Y) :
      Set ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y)) :=
  TopCat.ofHom ⟨fun ⟨⟨x, hxn⟩, hxprev⟩ =>
    ⟨⟨f x, hf.mapsTo_skeleton n hxn⟩, hf.mapsTo_skeleton (n - 1) hxprev⟩,
    by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact f.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

end CWHomology
end CWComplex.SkeletonHomology
end
