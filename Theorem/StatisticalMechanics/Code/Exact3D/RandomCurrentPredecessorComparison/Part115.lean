/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part107
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt_of_cell_eq_empty
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell_empty :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = ∅) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = ∅ := by
    simpa [cell, Ωactive, w, G] using hcell_empty
  have hfalse : ∀ m : {m : Profile // m ∈ cell}, False := by
    intro m
    have hmem : m.1 ∈ (∅ : Finset Profile) := by
      simpa [hcell] using m.2
    cases hmem
  let split : {m : Profile // m ∈ cell} → Finset Empty := fun _ => ∅
  let route :
      (m : {m : Profile // m ∈ cell}) → Empty →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun _ i => Empty.elim i
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt]
  refine ⟨Empty, split, route, ?_, ?_⟩
  · intro p _hp _q _hq _hroute
    exact Empty.elim p.2
  · intro m hm
    exact False.elim
      (hfalse ⟨m, by simpa [cell, Ωactive, w, G] using hm⟩)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt_of_cell_eq_empty
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell_empty :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = ∅) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = ∅ := by
    simpa [cell, Ωactive, w, G] using hcell_empty
  have hfalse : ∀ m : {m : Profile // m ∈ cell}, False := by
    intro m
    have hmem : m.1 ∈ (∅ : Finset Profile) := by
      simpa [hcell] using m.2
    cases hmem
  let split : {m : Profile // m ∈ cell} → Finset Empty := fun _ => ∅
  let route :
      (m : {m : Profile // m ∈ cell}) → Empty →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
    fun _ i => Empty.elim i
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt]
  refine ⟨Empty, split, route, ?_, ?_⟩
  · intro p _hp _q _hq _hroute
    exact Empty.elim p.2
  · intro m hm
    exact False.elim
      (hfalse ⟨m, by simpa [cell, Ωactive, w, G] using hm⟩)

set_option maxHeartbeats 300000 in


set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt_of_sourceEquationFiniteCellRouteShareAtEdgeBoundsAt
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt]
    at hcell
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt]
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  rcases hcell with
    ⟨profileRoute, witness, hinjProfile, hleft, hright, hpoint⟩
  have hwitness :
      ∀ a : {m : Profile // m ∈ cell},
        witness a ∈
          edgeCopySourcePairWitnesses G
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) (profileRoute a) := by
    intro a
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨hleft a, hright a⟩
  let split : {m : Profile // m ∈ cell} → Finset Unit := fun _ => {()}
  let route :
      (m : {m : Profile // m ∈ cell}) → Unit →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun a _ => edgeCopySourcePairData_of_witness G (hwitness a)
  refine ⟨Unit, split, route, ?_, ?_⟩
  · intro p _hp q _hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        cases i
        cases j
        have hab : a = b := by
          exact hinjProfile (by
            simpa [route] using congrArg Sigma.fst hroute)
        cases hab
        rfl
  · intro m hm
    simpa [split, route, G] using hpoint m hm

set_option maxHeartbeats 300000 in


set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt_of_sourceEquationFiniteCellRouteShareAtEdgeBoundsAt
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt]
    at hcell
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt]
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  rcases hcell with
    ⟨profileRoute, witness, hinjProfile, hleft, hright, hpoint⟩
  have hwitness :
      ∀ a : {m : Profile // m ∈ cell},
        witness a ∈
          edgeCopySourcePairWitnesses G
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) (profileRoute a) := by
    intro a
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨hleft a, hright a⟩
  let split : {m : Profile // m ∈ cell} → Finset Unit := fun _ => {()}
  let route :
      (m : {m : Profile // m ∈ cell}) → Unit →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
    fun a _ => edgeCopySourcePairData_of_witness G (hwitness a)
  refine ⟨Unit, split, route, ?_, ?_⟩
  · intro p _hp q _hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        cases i
        cases j
        have hab : a = b := by
          exact hinjProfile (by
            simpa [route] using congrArg Sigma.fst hroute)
        cases hab
        rfl
  · intro m hm
    simpa [split, route, G] using hpoint m hm

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt_of_cell_eq_empty
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell_empty :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = ∅) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = ∅ := by
    simpa [cell, Ωactive, w] using hcell_empty
  have hfalse : ∀ m : {m : Profile // m ∈ cell}, False := by
    intro m
    have hmem : m.1 ∈ (∅ : Finset Profile) := by
      simpa [hcell] using m.2
    cases hmem
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun m => False.elim (hfalse m)
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun m => False.elim (hfalse m)
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a _b _h
    exact False.elim (hfalse a)
  · intro m
    exact False.elim (hfalse m)
  · intro m
    exact False.elim (hfalse m)
  · intro m hm
    exact False.elim
      (hfalse ⟨m, by simpa [cell, Ωactive, w] using hm⟩)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt_of_cell_eq_empty
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell_empty :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = ∅) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = ∅ := by
    simpa [cell, Ωactive, w] using hcell_empty
  have hfalse : ∀ m : {m : Profile // m ∈ cell}, False := by
    intro m
    have hmem : m.1 ∈ (∅ : Finset Profile) := by
      simpa [hcell] using m.2
    cases hmem
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun m => False.elim (hfalse m)
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun m => False.elim (hfalse m)
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a _b _h
    exact False.elim (hfalse a)
  · intro m
    exact False.elim (hfalse m)
  · intro m
    exact False.elim (hfalse m)
  · intro m hm
    exact False.elim
      (hfalse ⟨m, by simpa [cell, Ωactive, w] using hm⟩)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt_of_cell_eq_singleton
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_singleton :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0})
    (profile0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (witness0 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile0))
    (hleft :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        witness0 =
        doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile0)) \
          witness0) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile0)) /
          384) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = {m0} := by
    simpa [cell, Ωactive, w] using hcell_singleton
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun _ => profile0
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun _ => witness0
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a b _h
    apply Subtype.ext
    have ha : a.1 ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact a.2
    have hb : b.1 ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact b.2
    exact (Finset.mem_singleton.mp ha).trans
      (Finset.mem_singleton.mp hb).symm
  · intro m
    simpa [profileRoute, witness] using hleft
  · intro m
    simpa [profileRoute, witness] using hright
  · intro m hm
    have hm_singleton : m ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact hm
    have hm_eq : m = m0 := Finset.mem_singleton.mp hm_singleton
    subst m
    simpa [profileRoute, w] using hpoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt_of_cell_eq_singleton
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_singleton :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0})
    (profile0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (witness0 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile0))
    (hleft :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        witness0 =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile0)) \
          witness0) =
        doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          e0 ew m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile0)) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = {m0} := by
    simpa [cell, Ωactive, w] using hcell_singleton
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun _ => profile0
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun _ => witness0
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a b _h
    apply Subtype.ext
    have ha : a.1 ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact a.2
    have hb : b.1 ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact b.2
    exact (Finset.mem_singleton.mp ha).trans
      (Finset.mem_singleton.mp hb).symm
  · intro m
    simpa [profileRoute, witness, w] using hleft
  · intro m
    simpa [profileRoute, witness, w] using hright
  · intro m hm
    have hm_singleton : m ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact hm
    have hm_eq : m = m0 := Finset.mem_singleton.mp hm_singleton
    subst m
    simpa [profileRoute, w] using hpoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt_of_cell_eq_singleton
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_singleton :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0})
    {Split : Type}
    (split0 : Finset Split)
    (route0 :
      Split →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hinj0 : Set.InjOn route0 split0)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew m0 ≤
        ∑ i ∈ split0,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (route0 i)) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = {m0} := by
    simpa [cell, Ωactive, w, G] using hcell_singleton
  let split : {m : Profile // m ∈ cell} → Finset Split := fun _ => split0
  let route :
      (m : {m : Profile // m ∈ cell}) → Split →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun _ i => route0 i
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt]
  refine ⟨Split, split, route, ?_, ?_⟩
  · intro p hp q hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        have hi_mem : i ∈ split0 := by
          simpa [Finset.mem_sigma, split] using hp
        have hj_mem : j ∈ split0 := by
          simpa [Finset.mem_sigma, split] using hq
        have hij : i = j := by
          exact hinj0 hi_mem hj_mem (by
            simpa [route, G] using hroute)
        have hab : a = b := by
          apply Subtype.ext
          have ha : a.1 ∈ ({m0} : Finset Profile) := by
            rw [← hcell]
            exact a.2
          have hb : b.1 ∈ ({m0} : Finset Profile) := by
            rw [← hcell]
            exact b.2
          exact (Finset.mem_singleton.mp ha).trans
            (Finset.mem_singleton.mp hb).symm
        cases hab
        cases hij
        rfl
  · intro m hm
    have hm_singleton : m ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact hm
    have hm_eq : m = m0 := Finset.mem_singleton.mp hm_singleton
    subst m
    simpa [split, route, G, w] using hpoint0

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt_of_cell_eq_singleton
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_singleton :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0})
    {Split : Type}
    (split0 : Finset Split)
    (route0 :
      Split →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hinj0 : Set.InjOn route0 split0)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          e0 ew m0 ≤
        ∑ i ∈ split0,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (route0 i)) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = {m0} := by
    simpa [cell, Ωactive, w, G] using hcell_singleton
  let split : {m : Profile // m ∈ cell} → Finset Split := fun _ => split0
  let route :
      (m : {m : Profile // m ∈ cell}) → Split →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
    fun _ i => route0 i
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt]
  refine ⟨Split, split, route, ?_, ?_⟩
  · intro p hp q hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        have hi_mem : i ∈ split0 := by
          simpa [Finset.mem_sigma, split] using hp
        have hj_mem : j ∈ split0 := by
          simpa [Finset.mem_sigma, split] using hq
        have hij : i = j := by
          exact hinj0 hi_mem hj_mem (by
            simpa [route, G] using hroute)
        have hab : a = b := by
          apply Subtype.ext
          have ha : a.1 ∈ ({m0} : Finset Profile) := by
            rw [← hcell]
            exact a.2
          have hb : b.1 ∈ ({m0} : Finset Profile) := by
            rw [← hcell]
            exact b.2
          exact (Finset.mem_singleton.mp ha).trans
            (Finset.mem_singleton.mp hb).symm
        cases hab
        cases hij
        rfl
  · intro m hm
    have hm_singleton : m ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact hm
    have hm_eq : m = m0 := Finset.mem_singleton.mp hm_singleton
    subst m
    simpa [split, route, G, w] using hpoint0

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_of_cell_eq_empty
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell_empty :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = ∅) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = ∅ := by
    simpa [cell, Ωactive, w, G] using hcell_empty
  have hfalse : ∀ m : {m : Profile // m ∈ cell}, False := by
    intro m
    have hmem : m.1 ∈ (∅ : Finset Profile) := by
      simpa [hcell] using m.2
    cases hmem
  let split : {m : Profile // m ∈ cell} → Finset Empty := fun _ => ∅
  let route :
      (m : {m : Profile // m ∈ cell}) → Empty →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun _ i => Empty.elim i
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt]
  refine ⟨Empty, split, route, ?_, ?_⟩
  · intro p _hp _q _hq _hroute
    exact Empty.elim p.2
  · intro m hm
    exact False.elim
      (hfalse ⟨m, by simpa [cell, Ωactive, w, G] using hm⟩)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_of_cell_eq_empty
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell_empty :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = ∅) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = ∅ := by
    simpa [cell, Ωactive, w, G] using hcell_empty
  have hfalse : ∀ m : {m : Profile // m ∈ cell}, False := by
    intro m
    have hmem : m.1 ∈ (∅ : Finset Profile) := by
      simpa [hcell] using m.2
    cases hmem
  let split : {m : Profile // m ∈ cell} → Finset Empty := fun _ => ∅
  let route :
      (m : {m : Profile // m ∈ cell}) → Empty →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
    fun _ i => Empty.elim i
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt]
  refine ⟨Empty, split, route, ?_, ?_⟩
  · intro p _hp _q _hq _hroute
    exact Empty.elim p.2
  · intro m hm
    exact False.elim
      (hfalse ⟨m, by simpa [cell, Ωactive, w, G] using hm⟩)

set_option maxHeartbeats 300000 in


set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_of_sourceEquationFiniteCellRouteShareBoundsAt
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt]
    at hcell
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt]
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  rcases hcell with
    ⟨profileRoute, witness, hinjProfile, hleft, hright, hpoint⟩
  have hwitness :
      ∀ a : {m : Profile // m ∈ cell},
        witness a ∈
          edgeCopySourcePairWitnesses G
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) (profileRoute a) := by
    intro a
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨hleft a, hright a⟩
  let split : {m : Profile // m ∈ cell} → Finset Unit := fun _ => {()}
  let route :
      (m : {m : Profile // m ∈ cell}) → Unit →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun a _ => edgeCopySourcePairData_of_witness G (hwitness a)
  refine ⟨Unit, split, route, ?_, ?_⟩
  · intro p _hp q _hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        cases i
        cases j
        have hab : a = b := by
          exact hinjProfile (by
            simpa [route] using congrArg Sigma.fst hroute)
        cases hab
        rfl
  · intro m hm
    simpa [split, route, G] using hpoint m hm

set_option maxHeartbeats 300000 in


set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_of_sourceEquationFiniteCellRouteShareBoundsAt
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt]
    at hcell
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt]
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  rcases hcell with
    ⟨profileRoute, witness, hinjProfile, hleft, hright, hpoint⟩
  have hwitness :
      ∀ a : {m : Profile // m ∈ cell},
        witness a ∈
          edgeCopySourcePairWitnesses G
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) (profileRoute a) := by
    intro a
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨hleft a, hright a⟩
  let split : {m : Profile // m ∈ cell} → Finset Unit := fun _ => {()}
  let route :
      (m : {m : Profile // m ∈ cell}) → Unit →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
    fun a _ => edgeCopySourcePairData_of_witness G (hwitness a)
  refine ⟨Unit, split, route, ?_, ?_⟩
  · intro p _hp q _hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        cases i
        cases j
        have hab : a = b := by
          exact hinjProfile (by
            simpa [route] using congrArg Sigma.fst hroute)
        cases hab
        rfl
  · intro m hm
    simpa [split, route, G] using hpoint m hm

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_of_cell_eq_singleton
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_singleton :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0})
    {Split : Type}
    (split0 : Finset Split)
    (route0 :
      Split →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hinj0 : Set.InjOn route0 split0)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ∑ i ∈ split0,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (route0 i)) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = {m0} := by
    simpa [cell, Ωactive, w, G] using hcell_singleton
  let split : {m : Profile // m ∈ cell} → Finset Split := fun _ => split0
  let route :
      (m : {m : Profile // m ∈ cell}) → Split →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun _ i => route0 i
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt]
  refine ⟨Split, split, route, ?_, ?_⟩
  · intro p hp q hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        have hi_mem : i ∈ split0 := by
          simpa [Finset.mem_sigma, split] using hp
        have hj_mem : j ∈ split0 := by
          simpa [Finset.mem_sigma, split] using hq
        have hij : i = j := by
          exact hinj0 hi_mem hj_mem (by
            simpa [route, G] using hroute)
        have hab : a = b := by
          apply Subtype.ext
          have ha : a.1 ∈ ({m0} : Finset Profile) := by
            rw [← hcell]
            exact a.2
          have hb : b.1 ∈ ({m0} : Finset Profile) := by
            rw [← hcell]
            exact b.2
          exact (Finset.mem_singleton.mp ha).trans
            (Finset.mem_singleton.mp hb).symm
        cases hab
        cases hij
        rfl
  · intro m hm
    have hm_singleton : m ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact hm
    have hm_eq : m = m0 := Finset.mem_singleton.mp hm_singleton
    subst m
    simpa [split, route, G, w] using hpoint0

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_of_cell_eq_singleton
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_singleton :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0})
    {Split : Type}
    (split0 : Finset Split)
    (route0 :
      Split →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hinj0 : Set.InjOn route0 split0)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ∑ i ∈ split0,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (route0 i)) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = {m0} := by
    simpa [cell, Ωactive, w, G] using hcell_singleton
  let split : {m : Profile // m ∈ cell} → Finset Split := fun _ => split0
  let route :
      (m : {m : Profile // m ∈ cell}) → Split →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
    fun _ i => route0 i
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt]
  refine ⟨Split, split, route, ?_, ?_⟩
  · intro p hp q hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        have hi_mem : i ∈ split0 := by
          simpa [Finset.mem_sigma, split] using hp
        have hj_mem : j ∈ split0 := by
          simpa [Finset.mem_sigma, split] using hq
        have hij : i = j := by
          exact hinj0 hi_mem hj_mem (by
            simpa [route, G] using hroute)
        have hab : a = b := by
          apply Subtype.ext
          have ha : a.1 ∈ ({m0} : Finset Profile) := by
            rw [← hcell]
            exact a.2
          have hb : b.1 ∈ ({m0} : Finset Profile) := by
            rw [← hcell]
            exact b.2
          exact (Finset.mem_singleton.mp ha).trans
            (Finset.mem_singleton.mp hb).symm
        cases hab
        cases hij
        rfl
  · intro m hm
    have hm_singleton : m ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact hm
    have hm_eq : m = m0 := Finset.mem_singleton.mp hm_singleton
    subst m
    simpa [split, route, G, w] using hpoint0

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_of_cell_subset_finset
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {rows : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ rows)
    {Split : Type}
    (splitRows :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows} →
        Finset Split)
    (routeRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
        m ∈ rows}) →
        Split →
          edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hinjRows :
      Set.InjOn
        (fun p :
            Sigma
              (fun _ :
                {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                  m ∈ rows} =>
                Split) =>
          routeRows p.1 p.2)
        (rows.attach.sigma splitRows))
    (hpointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ∑ i ∈ splitRows ⟨m, hm⟩,
              ((β / 6) *
                edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (routeRows ⟨m, hm⟩ i)) /
                384) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hsubset : ∀ m : Profile, m ∈ cell → m ∈ rows := by
    simpa [cell, Ωactive, w, G] using hcell_subset
  let toRows : {m : Profile // m ∈ cell} → {m : Profile // m ∈ rows} :=
    fun m => ⟨m.1, hsubset m.1 m.2⟩
  let split : {m : Profile // m ∈ cell} → Finset Split :=
    fun m => splitRows (toRows m)
  let route :
      (m : {m : Profile // m ∈ cell}) → Split →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun m i => routeRows (toRows m) i
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt]
  refine ⟨Split, split, route, ?_, ?_⟩
  · intro p hp q hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        have hpRows :
            (Sigma.mk (toRows a) i :
                Sigma (fun _ : {m : Profile // m ∈ rows} => Split)) ∈
              rows.attach.sigma splitRows := by
          simpa [Finset.mem_sigma, toRows, split] using hp
        have hqRows :
            (Sigma.mk (toRows b) j :
                Sigma (fun _ : {m : Profile // m ∈ rows} => Split)) ∈
              rows.attach.sigma splitRows := by
          simpa [Finset.mem_sigma, toRows, split] using hq
        have hrouteRows :
            routeRows (toRows a) i = routeRows (toRows b) j := by
          simpa [route, toRows, G] using hroute
        have hrows :
            (Sigma.mk (toRows a) i :
                Sigma (fun _ : {m : Profile // m ∈ rows} => Split)) =
              Sigma.mk (toRows b) j :=
          hinjRows hpRows hqRows hrouteRows
        have hfst : toRows a = toRows b := congrArg Sigma.fst hrows
        have hab : a = b := by
          apply Subtype.ext
          exact
            congrArg (fun x : {m : Profile // m ∈ rows} => x.1) hfst
        cases hab
        have hij : i = j := by
          cases hrows
          rfl
        cases hij
        rfl
  · intro m hm
    have hm_rows : m ∈ rows := hsubset m hm
    simpa [split, route, toRows, G, w] using hpointRows m hm_rows

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_of_cell_subset_finset
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {rows : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ rows)
    {Split : Type}
    (splitRows :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows} →
        Finset Split)
    (routeRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
        m ∈ rows}) →
        Split →
          edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hinjRows :
      Set.InjOn
        (fun p :
            Sigma
              (fun _ :
                {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                  m ∈ rows} =>
                Split) =>
          routeRows p.1 p.2)
        (rows.attach.sigma splitRows))
    (hpointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
            ∑ i ∈ splitRows ⟨m, hm⟩,
              ((β / 6) *
                edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (routeRows ⟨m, hm⟩ i)) /
                384) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hsubset : ∀ m : Profile, m ∈ cell → m ∈ rows := by
    simpa [cell, Ωactive, w, G] using hcell_subset
  let toRows : {m : Profile // m ∈ cell} → {m : Profile // m ∈ rows} :=
    fun m => ⟨m.1, hsubset m.1 m.2⟩
  let split : {m : Profile // m ∈ cell} → Finset Split :=
    fun m => splitRows (toRows m)
  let route :
      (m : {m : Profile // m ∈ cell}) → Split →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
    fun m i => routeRows (toRows m) i
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt]
  refine ⟨Split, split, route, ?_, ?_⟩
  · intro p hp q hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        have hpRows :
            (Sigma.mk (toRows a) i :
                Sigma (fun _ : {m : Profile // m ∈ rows} => Split)) ∈
              rows.attach.sigma splitRows := by
          simpa [Finset.mem_sigma, toRows, split] using hp
        have hqRows :
            (Sigma.mk (toRows b) j :
                Sigma (fun _ : {m : Profile // m ∈ rows} => Split)) ∈
              rows.attach.sigma splitRows := by
          simpa [Finset.mem_sigma, toRows, split] using hq
        have hrouteRows :
            routeRows (toRows a) i = routeRows (toRows b) j := by
          simpa [route, toRows, G] using hroute
        have hrows :
            (Sigma.mk (toRows a) i :
                Sigma (fun _ : {m : Profile // m ∈ rows} => Split)) =
              Sigma.mk (toRows b) j :=
          hinjRows hpRows hqRows hrouteRows
        have hfst : toRows a = toRows b := congrArg Sigma.fst hrows
        have hab : a = b := by
          apply Subtype.ext
          exact
            congrArg (fun x : {m : Profile // m ∈ rows} => x.1) hfst
        cases hab
        have hij : i = j := by
          cases hrows
          rfl
        cases hij
        rfl
  · intro m hm
    have hm_rows : m ∈ rows := hsubset m hm
    simpa [split, route, toRows, G, w] using hpointRows m hm_rows

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_of_cell_eq_finset
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {rows : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hcell_rows :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = rows)
    {Split : Type}
    (splitRows :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows} →
        Finset Split)
    (routeRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
        m ∈ rows}) →
        Split →
          edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hinjRows :
      Set.InjOn
        (fun p :
            Sigma
              (fun _ :
                {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                  m ∈ rows} =>
                Split) =>
          routeRows p.1 p.2)
        (rows.attach.sigma splitRows))
    (hpointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ∑ i ∈ splitRows ⟨m, hm⟩,
              ((β / 6) *
                edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (routeRows ⟨m, hm⟩ i)) /
                384) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  refine
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_of_cell_subset_finset
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew) (rows := rows) ?_
      splitRows routeRows hinjRows hpointRows
  dsimp
  intro m hm
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = rows := by
    simpa [cell, Ωactive, w, G] using hcell_rows
  have hm_cell : m ∈ cell := by
    simpa [cell, Ωactive, w, G] using hm
  rw [← hcell]
  exact hm_cell

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_of_cell_eq_finset
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {rows : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hcell_rows :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = rows)
    {Split : Type}
    (splitRows :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows} →
        Finset Split)
    (routeRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
        m ∈ rows}) →
        Split →
          edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hinjRows :
      Set.InjOn
        (fun p :
            Sigma
              (fun _ :
                {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                  m ∈ rows} =>
                Split) =>
          routeRows p.1 p.2)
        (rows.attach.sigma splitRows))
    (hpointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
            ∑ i ∈ splitRows ⟨m, hm⟩,
              ((β / 6) *
                edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (routeRows ⟨m, hm⟩ i)) /
                384) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  refine
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_of_cell_subset_finset
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew) (rows := rows) ?_
      splitRows routeRows hinjRows hpointRows
  dsimp
  intro m hm
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = rows := by
    simpa [cell, Ωactive, w, G] using hcell_rows
  have hm_cell : m ∈ cell := by
    simpa [cell, Ωactive, w, G] using hm
  rw [← hcell]
  exact hm_cell

set_option maxHeartbeats 1000000 in

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_of_cell_subset_pair_pointwise
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 m1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ ({m0, m1} : Finset Profile))
    {Split : Type}
    (split0 split1 : Finset Split)
    (route0 route1 :
      Split →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hinj0 : Set.InjOn route0 split0)
    (hinj1 : Set.InjOn route1 split1)
    (hdisj : ∀ i ∈ split0, ∀ j ∈ split1, route0 i ≠ route1 j)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ∑ i ∈ split0,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (route0 i)) /
            384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ∑ i ∈ split1,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (route1 i)) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Profile := ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ
  let rows : Finset Profile := {m0, m1}
  let splitRows : {m : Profile // m ∈ rows} → Finset Split :=
    fun m => if m.1 = m0 then split0 else split1
  let routeRows :
      (m : {m : Profile // m ∈ rows}) → Split →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun m i => if m.1 = m0 then route0 i else route1 i
  have hinjRows :
      Set.InjOn
        (fun p : Sigma (fun _ : {m : Profile // m ∈ rows} => Split) =>
          routeRows p.1 p.2)
        (rows.attach.sigma splitRows) := by
    intro p hp q hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        by_cases ha0 : a.1 = m0
        · by_cases hb0 : b.1 = m0
          · have hi : i ∈ split0 := by
              simpa [Finset.mem_sigma, splitRows, ha0] using hp
            have hj : j ∈ split0 := by
              simpa [Finset.mem_sigma, splitRows, hb0] using hq
            have hij : i = j := by
              exact hinj0 hi hj (by
                simpa [routeRows, ha0, hb0] using hroute)
            have hab : a = b := by
              apply Subtype.ext
              exact ha0.trans hb0.symm
            cases hab
            cases hij
            rfl
          · have hi : i ∈ split0 := by
              simpa [Finset.mem_sigma, splitRows, ha0] using hp
            have hj : j ∈ split1 := by
              simpa [Finset.mem_sigma, splitRows, hb0] using hq
            exact False.elim
              (hdisj i hi j hj (by
                simpa [routeRows, ha0, hb0] using hroute))
        · by_cases hb0 : b.1 = m0
          · have hi : i ∈ split1 := by
              simpa [Finset.mem_sigma, splitRows, ha0] using hp
            have hj : j ∈ split0 := by
              simpa [Finset.mem_sigma, splitRows, hb0] using hq
            have hroute' : route0 j = route1 i := by
              simpa [routeRows, ha0, hb0] using hroute.symm
            exact False.elim (hdisj j hj i hi hroute')
          · have hi : i ∈ split1 := by
              simpa [Finset.mem_sigma, splitRows, ha0] using hp
            have hj : j ∈ split1 := by
              simpa [Finset.mem_sigma, splitRows, hb0] using hq
            have hij : i = j := by
              exact hinj1 hi hj (by
                simpa [routeRows, ha0, hb0] using hroute)
            have ha_pair : a.1 ∈ ({m0, m1} : Finset Profile) := by
              change a.1 ∈ rows
              exact a.2
            have hb_pair : b.1 ∈ ({m0, m1} : Finset Profile) := by
              change b.1 ∈ rows
              exact b.2
            have ha_or : a.1 = m0 ∨ a.1 = m1 := by
              rcases Finset.mem_insert.mp ha_pair with ha | ha
              · exact Or.inl ha
              · exact Or.inr (Finset.mem_singleton.mp ha)
            have hb_or : b.1 = m0 ∨ b.1 = m1 := by
              rcases Finset.mem_insert.mp hb_pair with hb | hb
              · exact Or.inl hb
              · exact Or.inr (Finset.mem_singleton.mp hb)
            have hab : a = b := by
              apply Subtype.ext
              exact (ha_or.resolve_left ha0).trans
                (hb_or.resolve_left hb0).symm
            cases hab
            cases hij
            rfl
  have hpointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ∑ i ∈ splitRows ⟨m, hm⟩,
              ((β / 6) *
                edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (routeRows ⟨m, hm⟩ i)) /
                384 := by
    intro m hm
    by_cases hm0 : m = m0
    · subst m
      simpa [splitRows, routeRows] using hpoint0
    · have hm_pair : m ∈ ({m0, m1} : Finset Profile) := by
        simpa [rows] using hm
      have hm_or : m = m0 ∨ m = m1 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hm_pair
      have hm1 : m = m1 := hm_or.resolve_left hm0
      subst m
      simpa [splitRows, routeRows, hm0] using hpoint1
  exact
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_of_cell_subset_finset
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (rows := rows) (by simpa [rows] using hcell_subset)
      splitRows routeRows hinjRows hpointRows

set_option maxHeartbeats 1000000 in

open Classical in
set_option linter.style.longLine false in

theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_of_cell_subset_pair_pointwise
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 m1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ ({m0, m1} : Finset Profile))
    {Split : Type}
    (split0 split1 : Finset Split)
    (route0 route1 :
      Split →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hinj0 : Set.InjOn route0 split0)
    (hinj1 : Set.InjOn route1 split1)
    (hdisj : ∀ i ∈ split0, ∀ j ∈ split1, route0 i ≠ route1 j)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ∑ i ∈ split0,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (route0 i)) /
            384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ∑ i ∈ split1,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (route1 i)) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Profile := ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ
  let rows : Finset Profile := {m0, m1}
  let splitRows : {m : Profile // m ∈ rows} → Finset Split :=
    fun m => if m.1 = m0 then split0 else split1
  let routeRows :
      (m : {m : Profile // m ∈ rows}) → Split →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :=
    fun m i => if m.1 = m0 then route0 i else route1 i
  have hinjRows :
      Set.InjOn
        (fun p : Sigma (fun _ : {m : Profile // m ∈ rows} => Split) =>
          routeRows p.1 p.2)
        (rows.attach.sigma splitRows) := by
    intro p hp q hq hroute
    cases p with
    | mk a i =>
      cases q with
      | mk b j =>
        by_cases ha0 : a.1 = m0
        · by_cases hb0 : b.1 = m0
          · have hi : i ∈ split0 := by
              simpa [Finset.mem_sigma, splitRows, ha0] using hp
            have hj : j ∈ split0 := by
              simpa [Finset.mem_sigma, splitRows, hb0] using hq
            have hij : i = j := by
              exact hinj0 hi hj (by
                simpa [routeRows, ha0, hb0] using hroute)
            have hab : a = b := by
              apply Subtype.ext
              exact ha0.trans hb0.symm
            cases hab
            cases hij
            rfl
          · have hi : i ∈ split0 := by
              simpa [Finset.mem_sigma, splitRows, ha0] using hp
            have hj : j ∈ split1 := by
              simpa [Finset.mem_sigma, splitRows, hb0] using hq
            exact False.elim
              (hdisj i hi j hj (by
                simpa [routeRows, ha0, hb0] using hroute))
        · by_cases hb0 : b.1 = m0
          · have hi : i ∈ split1 := by
              simpa [Finset.mem_sigma, splitRows, ha0] using hp
            have hj : j ∈ split0 := by
              simpa [Finset.mem_sigma, splitRows, hb0] using hq
            have hroute' : route0 j = route1 i := by
              simpa [routeRows, ha0, hb0] using hroute.symm
            exact False.elim (hdisj j hj i hi hroute')
          · have hi : i ∈ split1 := by
              simpa [Finset.mem_sigma, splitRows, ha0] using hp
            have hj : j ∈ split1 := by
              simpa [Finset.mem_sigma, splitRows, hb0] using hq
            have hij : i = j := by
              exact hinj1 hi hj (by
                simpa [routeRows, ha0, hb0] using hroute)
            have ha_pair : a.1 ∈ ({m0, m1} : Finset Profile) := by
              change a.1 ∈ rows
              exact a.2
            have hb_pair : b.1 ∈ ({m0, m1} : Finset Profile) := by
              change b.1 ∈ rows
              exact b.2
            have ha_or : a.1 = m0 ∨ a.1 = m1 := by
              rcases Finset.mem_insert.mp ha_pair with ha | ha
              · exact Or.inl ha
              · exact Or.inr (Finset.mem_singleton.mp ha)
            have hb_or : b.1 = m0 ∨ b.1 = m1 := by
              rcases Finset.mem_insert.mp hb_pair with hb | hb
              · exact Or.inl hb
              · exact Or.inr (Finset.mem_singleton.mp hb)
            have hab : a = b := by
              apply Subtype.ext
              exact (ha_or.resolve_left ha0).trans
                (hb_or.resolve_left hb0).symm
            cases hab
            cases hij
            rfl
  have hpointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
            ∑ i ∈ splitRows ⟨m, hm⟩,
              ((β / 6) *
                edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (routeRows ⟨m, hm⟩ i)) /
                384 := by
    intro m hm
    by_cases hm0 : m = m0
    · subst m
      simpa [splitRows, routeRows] using hpoint0
    · have hm_pair : m ∈ ({m0, m1} : Finset Profile) := by
        simpa [rows] using hm
      have hm_or : m = m0 ∨ m = m1 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hm_pair
      have hm1 : m = m1 := hm_or.resolve_left hm0
      subst m
      simpa [splitRows, routeRows, hm0] using hpoint1
  exact
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_of_cell_subset_finset
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (rows := rows) (by simpa [rows] using hcell_subset)
      splitRows routeRows hinjRows hpointRows

open Classical in
set_option linter.style.longLine false in


theorem finset_pair_attach_sigma_if_route_injOn
    {α Data Split : Type*} [DecidableEq α]
    {m0 m1 : α}
    (split0 split1 : Finset Split)
    (route0 route1 : Split → Data)
    (hinj0 : Set.InjOn route0 split0)
    (hinj1 : Set.InjOn route1 split1)
    (hdisj : ∀ i ∈ split0, ∀ j ∈ split1, route0 i ≠ route1 j) :
    Set.InjOn
      (fun p :
          Sigma
            (fun _ : {m : α // m ∈ ({m0, m1} : Finset α)} => Split) =>
        if p.1.1 = m0 then route0 p.2 else route1 p.2)
      (({m0, m1} : Finset α).attach.sigma
        (fun m : {m : α // m ∈ ({m0, m1} : Finset α)} =>
          if m.1 = m0 then split0 else split1)) := by
  intro p hp q hq hroute
  cases p with
  | mk a i =>
    cases q with
    | mk b j =>
      by_cases ha0 : a.1 = m0
      · by_cases hb0 : b.1 = m0
        · have hi : i ∈ split0 := by
            have hi_mem := (Finset.mem_sigma.mp hp).2
            simpa [ha0] using hi_mem
          have hj : j ∈ split0 := by
            have hj_mem := (Finset.mem_sigma.mp hq).2
            simpa [hb0] using hj_mem
          have hij : i = j := by
            exact hinj0 hi hj (by simpa [ha0, hb0] using hroute)
          have hab : a = b := by
            apply Subtype.ext
            exact ha0.trans hb0.symm
          cases hab
          cases hij
          rfl
        · have hi : i ∈ split0 := by
            have hi_mem := (Finset.mem_sigma.mp hp).2
            simpa [ha0] using hi_mem
          have hj : j ∈ split1 := by
            have hj_mem := (Finset.mem_sigma.mp hq).2
            simpa [hb0] using hj_mem
          exact False.elim (hdisj i hi j hj (by simpa [ha0, hb0] using hroute))
      · by_cases hb0 : b.1 = m0
        · have hi : i ∈ split1 := by
            have hi_mem := (Finset.mem_sigma.mp hp).2
            simpa [ha0] using hi_mem
          have hj : j ∈ split0 := by
            have hj_mem := (Finset.mem_sigma.mp hq).2
            simpa [hb0] using hj_mem
          have hroute' : route0 j = route1 i := by
            simpa [ha0, hb0] using hroute.symm
          exact False.elim (hdisj j hj i hi hroute')
        · have hi : i ∈ split1 := by
            have hi_mem := (Finset.mem_sigma.mp hp).2
            simpa [ha0] using hi_mem
          have hj : j ∈ split1 := by
            have hj_mem := (Finset.mem_sigma.mp hq).2
            simpa [hb0] using hj_mem
          have hij : i = j := by
            exact hinj1 hi hj (by simpa [ha0, hb0] using hroute)
          have ha_pair : a.1 ∈ ({m0, m1} : Finset α) := a.2
          have hb_pair : b.1 ∈ ({m0, m1} : Finset α) := b.2
          have ha_or : a.1 = m0 ∨ a.1 = m1 := by
            rcases Finset.mem_insert.mp ha_pair with ha | ha
            · exact Or.inl ha
            · exact Or.inr (Finset.mem_singleton.mp ha)
          have hb_or : b.1 = m0 ∨ b.1 = m1 := by
            rcases Finset.mem_insert.mp hb_pair with hb | hb
            · exact Or.inl hb
            · exact Or.inr (Finset.mem_singleton.mp hb)
          have hab : a = b := by
            apply Subtype.ext
            exact (ha_or.resolve_left ha0).trans
              (hb_or.resolve_left hb0).symm
          cases hab
          cases hij
          rfl

open Classical in
set_option linter.style.longLine false in


theorem finset_singleton_attach_sigma_const_route_injOn
    {α Data Split : Type*}
    {m0 : α}
    (split0 : Finset Split)
    (route0 : Split → Data)
    (hinj0 : Set.InjOn route0 split0) :
    Set.InjOn
      (fun p :
          Sigma
            (fun _ : {m : α // m ∈ ({m0} : Finset α)} => Split) =>
        route0 p.2)
      (({m0} : Finset α).attach.sigma
        (fun _ : {m : α // m ∈ ({m0} : Finset α)} => split0)) := by
  intro p hp q hq hroute
  cases p with
  | mk a i =>
    cases q with
    | mk b j =>
      have hi : i ∈ split0 := (Finset.mem_sigma.mp hp).2
      have hj : j ∈ split0 := (Finset.mem_sigma.mp hq).2
      have hij : i = j := hinj0 hi hj hroute
      have hab : a = b := by
        apply Subtype.ext
        have ha0 : a.1 = m0 := by
          exact Finset.mem_singleton.mp a.2
        have hb0 : b.1 = m0 := by
          exact Finset.mem_singleton.mp b.2
        exact ha0.trans hb0.symm
      cases hab
      cases hij
      rfl

end Exact3D
end StatMech
