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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section16.Part2
open AlgebraicTopology CategoryTheory Limits AlgebraicTopologyI


noncomputable section

namespace CWComplex.SkeletonHomology

namespace CWHomology

/-- The induced map between relative singular chain complexes of the CW pairs
`(X_n, X_{n-1})` and `(Y_n, Y_{n-1})` arising from a cellular map. -/
def cellularRelativeChainMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    Excision.relativeSingularChainComplex
      ↥(CWComplex.skeleton X (n : ℕ∞) : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X)) ⟶
    Excision.relativeSingularChainComplex
      ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y)
      (Subtype.val ⁻¹' (CWComplex.skeleton Y ((↑(n - 1) : ℕ∞)) : Set Y)) :=
  cokernel.map _ _
    (Excision.singularChainZ.map (cellularMapOnPrevSkeleton f hf n))
    (Excision.singularChainZ.map (cellularMapOnSkeleton f hf n))
    (by
      show Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _ =
        Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _
      rw [← Excision.singularChainZ.map_comp, ← Excision.singularChainZ.map_comp,
        cellularMapSquare_comm])

/-- The induced map on relative singular homology
`H_n(X_n, X_{n-1}) → H_n(Y_n, Y_{n-1})` arising from a cellular map. -/
def relHomologySkeletonMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    relHomologySkeleton X n n ⟶ relHomologySkeleton Y n n :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map
    (cellularRelativeChainMap f hf n)

/-- The induced map on cellular chains `C_n(X) → C_n(Y)` arising from a cellular map,
obtained by transporting `relHomologySkeletonMap` along the cellular-chain
isomorphisms. -/
def skeletonAbsHomologyMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    skeletonHomology X n n ⟶ skeletonHomology Y n n :=
  HomologicalComplex.homologyMap
    (Excision.singularChainZ.map (cellularMapOnSkeleton f hf n)) n

/-- Naturality of the connecting homomorphism with respect to cellular maps. -/
noncomputable def singularHomologyMap (n : ℕ)
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    SingularHomologyGroup n X ⟶ SingularHomologyGroup n Y :=
  ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)

/-- The map on cellular homology `H_n(C_*(X)) → H_n(C_*(Y))` induced by a cellular map. -/
noncomputable def skeletonHomologyMapInduced (n : ℕ)
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) :
    skeletonHomology X (n + 1) n ⟶ skeletonHomology Y (n + 1) n :=
  ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
    (cellularMapOnSkeleton f hf (n + 1))

/-- A CW complex has *only even cells* if there are no cells of odd dimension. -/
def HasOnlyEvenCells (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Prop :=
  ∀ k : ℕ, IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) (2 * k + 1))

end CWHomology
end CWComplex.SkeletonHomology
end
