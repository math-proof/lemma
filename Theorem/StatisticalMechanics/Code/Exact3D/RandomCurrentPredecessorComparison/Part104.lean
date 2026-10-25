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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part96
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm : m ∈ Ωactive) :
    profileRoute ⟨m, hm⟩ ≠ m := by
  intro hprofile
  exact
    doubledBoxIncrementedFullSourceActive_sameProfileSourceEquationRoute_not_pointwise_div_six_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) (m := m) (profile := profileRoute ⟨m, hm⟩)
      (witness ⟨m, hm⟩) hedge (hrows m hm) hprofile
      (hleft ⟨m, hm⟩) (hright ⟨m, hm⟩) (hpoint m hm)

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_singleton_profileRoute_not_mem_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm : m ∈ Ωactive)
    (hsingleton : Ωactive = {m}) :
    profileRoute ⟨m, hm⟩ ∉ Ωactive := by
  classical
  have hne :
      profileRoute ⟨m, hm⟩ ≠ m :=
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint m hm
  intro hmem
  have hmem_singleton :
      profileRoute ⟨m, hm⟩ ∈
        ({m} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simpa [hsingleton] using hmem
  exact hne (Finset.mem_singleton.mp hmem_singleton)

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_pair_profileRoute_eq_other_of_mem_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (m₁ m₂ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm₁ : m₁ ∈ Ωactive) (hm₂ : m₂ ∈ Ωactive)
    (hpair :
      Ωactive =
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)))
    (hmem₁ : profileRoute ⟨m₁, hm₁⟩ ∈ Ωactive)
    (hmem₂ : profileRoute ⟨m₂, hm₂⟩ ∈ Ωactive) :
    profileRoute ⟨m₁, hm₁⟩ = m₂ ∧
      profileRoute ⟨m₂, hm₂⟩ = m₁ := by
  classical
  have hne₁ :
      profileRoute ⟨m₁, hm₁⟩ ≠ m₁ :=
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint m₁ hm₁
  have hne₂ :
      profileRoute ⟨m₂, hm₂⟩ ≠ m₂ :=
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint m₂ hm₂
  have hmem₁_pair :
      profileRoute ⟨m₁, hm₁⟩ ∈
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simpa [hpair] using hmem₁
  have hmem₂_pair :
      profileRoute ⟨m₂, hm₂⟩ ∈
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simpa [hpair] using hmem₂
  have hroute₁ : profileRoute ⟨m₁, hm₁⟩ = m₂ := by
    rcases Finset.mem_insert.mp hmem₁_pair with hself | hother
    · exact False.elim (hne₁ hself)
    · exact Finset.mem_singleton.mp hother
  have hroute₂ : profileRoute ⟨m₂, hm₂⟩ = m₁ := by
    rcases Finset.mem_insert.mp hmem₂_pair with hother | hself_mem
    · exact hother
    · have hself : profileRoute ⟨m₂, hm₂⟩ = m₂ :=
        Finset.mem_singleton.mp hself_mem
      exact False.elim (hne₂ hself)
  exact ⟨hroute₁, hroute₂⟩

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_pair_swap_or_external_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (m₁ m₂ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm₁ : m₁ ∈ Ωactive) (hm₂ : m₂ ∈ Ωactive)
    (hpair :
      Ωactive =
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))) :
    profileRoute ⟨m₁, hm₁⟩ ∉ Ωactive ∨
      profileRoute ⟨m₂, hm₂⟩ ∉ Ωactive ∨
        (profileRoute ⟨m₁, hm₁⟩ = m₂ ∧
          profileRoute ⟨m₂, hm₂⟩ = m₁) := by
  by_cases hmem₁ : profileRoute ⟨m₁, hm₁⟩ ∈ Ωactive
  · by_cases hmem₂ : profileRoute ⟨m₂, hm₂⟩ ∈ Ωactive
    · right
      right
      exact
        doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_pair_profileRoute_eq_other_of_mem_of_strictSectorYPredecessor3
          (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
          (e0 := e0) hedge hrows hleft hright hpoint m₁ m₂
          hm₁ hm₂ hpair hmem₁ hmem₂
    · right
      left
      exact hmem₂
  · left
    exact hmem₁

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_internal_injective_surjective_and_noFixed_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (hinj : Function.Injective profileRoute)
    (hinternal :
      ∀ m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
          profileRoute m ∈ Ωactive) :
    (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          ∃ m' :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
              profileRoute m' = m) ∧
      (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          profileRoute ⟨m, hm⟩ ≠ m) := by
  constructor
  · intro m hm
    exact
      finsetSubtype_internal_injective_route_surjective
        (Ω := Ωactive) (route := profileRoute) hinj hinternal m hm
  · intro m hm
    exact
      doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
        (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) hedge hrows hleft hright hpoint m hm

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_external_or_internal_cycle_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (hinj : Function.Injective profileRoute) :
    (∃ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∃ hm : m ∈ Ωactive,
          profileRoute ⟨m, hm⟩ ∉ Ωactive) ∨
      ((∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ _hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                profileRoute m' = m) ∧
        (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ hm : m ∈ Ωactive,
            profileRoute ⟨m, hm⟩ ≠ m) ∧
        (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ _hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                m'.1 ≠ m ∧ profileRoute m' = m)) := by
  classical
  by_cases hinternal :
      ∀ m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
          profileRoute m ∈ Ωactive
  · right
    have hperm :=
      doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_internal_injective_surjective_and_noFixed_of_strictSectorYPredecessor3
        (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) hedge hrows hleft hright hpoint hinj hinternal
    have hdistinct :
        ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                m'.1 ≠ m ∧ profileRoute m' = m := by
      intro m hm
      exact
        finsetSubtype_internal_injective_fixedPointFree_route_distinct_predecessor
          (Ω := Ωactive) (route := profileRoute) hinj hinternal
          hperm.2 m hm
    exact ⟨hperm.1, hperm.2, hdistinct⟩
  · left
    have hexternal :
        ∃ m :
          {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
            profileRoute m ∉ Ωactive := by
      simpa using (not_forall.mp hinternal)
    rcases hexternal with ⟨m, hmext⟩
    exact ⟨m.1, m.2, hmext⟩

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm : m ∈ Ωactive) :
    profileRoute ⟨m, hm⟩ ≠ m := by
  intro hprofile
  exact
    doubledBoxIncrementedFullSourceActive_sameProfileInnerPairSourceEquationRoute_not_pointwise_div_six_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) (m := m) (profile := profileRoute ⟨m, hm⟩)
      (witness ⟨m, hm⟩) hedge (hrows m hm) hprofile
      (hleft ⟨m, hm⟩) (hright ⟨m, hm⟩) (hpoint m hm)

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_external_or_internal_cycle_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (hinj : Function.Injective profileRoute) :
    (∃ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∃ hm : m ∈ Ωactive,
          profileRoute ⟨m, hm⟩ ∉ Ωactive) ∨
      ((∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ _hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                profileRoute m' = m) ∧
        (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ hm : m ∈ Ωactive,
            profileRoute ⟨m, hm⟩ ≠ m) ∧
        (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ _hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                m'.1 ≠ m ∧ profileRoute m' = m)) := by
  classical
  by_cases hinternal :
      ∀ m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
          profileRoute m ∈ Ωactive
  · right
    have hsurj :
        ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ _hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                profileRoute m' = m := by
      intro m hm
      exact
        finsetSubtype_internal_injective_route_surjective
          (Ω := Ωactive) (route := profileRoute) hinj hinternal m hm
    have hnofixed :
        ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ hm : m ∈ Ωactive,
            profileRoute ⟨m, hm⟩ ≠ m := by
      intro m hm
      exact
        doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
          (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
          (e0 := e0) hedge hrows hleft hright hpoint m hm
    have hdistinct :
        ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                m'.1 ≠ m ∧ profileRoute m' = m := by
      intro m hm
      exact
        finsetSubtype_internal_injective_fixedPointFree_route_distinct_predecessor
          (Ω := Ωactive) (route := profileRoute) hinj hinternal
          hnofixed m hm
    exact ⟨hsurj, hnofixed, hdistinct⟩
  · left
    have hexternal :
        ∃ m :
          {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
            profileRoute m ∉ Ωactive := by
      simpa using (not_forall.mp hinternal)
    rcases hexternal with ⟨m, hmext⟩
    exact ⟨m.1, m.2, hmext⟩

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_singleton_profileRoute_not_mem_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm : m ∈ Ωactive)
    (hsingleton : Ωactive = {m}) :
    profileRoute ⟨m, hm⟩ ∉ Ωactive := by
  classical
  have hne :
      profileRoute ⟨m, hm⟩ ≠ m :=
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint m hm
  intro hmem
  have hmem_singleton :
      profileRoute ⟨m, hm⟩ ∈
        ({m} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simpa [hsingleton] using hmem
  exact hne (Finset.mem_singleton.mp hmem_singleton)

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_pair_profileRoute_eq_other_of_mem_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (m₁ m₂ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm₁ : m₁ ∈ Ωactive) (hm₂ : m₂ ∈ Ωactive)
    (hpair :
      Ωactive =
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)))
    (hmem₁ : profileRoute ⟨m₁, hm₁⟩ ∈ Ωactive)
    (hmem₂ : profileRoute ⟨m₂, hm₂⟩ ∈ Ωactive) :
    profileRoute ⟨m₁, hm₁⟩ = m₂ ∧
      profileRoute ⟨m₂, hm₂⟩ = m₁ := by
  classical
  have hne₁ :
      profileRoute ⟨m₁, hm₁⟩ ≠ m₁ :=
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint m₁ hm₁
  have hne₂ :
      profileRoute ⟨m₂, hm₂⟩ ≠ m₂ :=
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint m₂ hm₂
  have hmem₁_pair :
      profileRoute ⟨m₁, hm₁⟩ ∈
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simpa [hpair] using hmem₁
  have hmem₂_pair :
      profileRoute ⟨m₂, hm₂⟩ ∈
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simpa [hpair] using hmem₂
  have hroute₁ : profileRoute ⟨m₁, hm₁⟩ = m₂ := by
    rcases Finset.mem_insert.mp hmem₁_pair with hself | hother
    · exact False.elim (hne₁ hself)
    · exact Finset.mem_singleton.mp hother
  have hroute₂ : profileRoute ⟨m₂, hm₂⟩ = m₁ := by
    rcases Finset.mem_insert.mp hmem₂_pair with hother | hself_mem
    · exact hother
    · have hself : profileRoute ⟨m₂, hm₂⟩ = m₂ :=
        Finset.mem_singleton.mp hself_mem
      exact False.elim (hne₂ hself)
  exact ⟨hroute₁, hroute₂⟩

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_pair_swap_or_external_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m))}
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          (witness m) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRoute m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
            witness m) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩)))
    (m₁ m₂ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm₁ : m₁ ∈ Ωactive) (hm₂ : m₂ ∈ Ωactive)
    (hpair :
      Ωactive =
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))) :
    profileRoute ⟨m₁, hm₁⟩ ∉ Ωactive ∨
      profileRoute ⟨m₂, hm₂⟩ ∉ Ωactive ∨
        (profileRoute ⟨m₁, hm₁⟩ = m₂ ∧
          profileRoute ⟨m₂, hm₂⟩ = m₁) := by
  by_cases hmem₁ : profileRoute ⟨m₁, hm₁⟩ ∈ Ωactive
  · by_cases hmem₂ : profileRoute ⟨m₂, hm₂⟩ ∈ Ωactive
    · right
      right
      exact
        doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_pair_profileRoute_eq_other_of_mem_of_strictSectorYPredecessor3
          (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
          (e0 := e0) hedge hrows hleft hright hpoint m₁ m₂
          hm₁ hm₂ hpair hmem₁ hmem₂
    · right
      left
      exact hmem₂
  · left
    exact hmem₁

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_external_or_internal_cycle
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hnonempty : Ωactive.Nonempty) :
    ∃ profileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      ∃ witness :
          (m :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive}) →
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) (profileRoute m)),
        (∀ m,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (FK.boxGraph 3 (2 * n)) (profileRoute m))
            (witness m) =
            doubledBoxOriginToInnerEndpointSource n v) ∧
          (∀ m,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (FK.boxGraph 3 (2 * n)) (profileRoute m))
              ((Finset.univ :
                  Finset
                    (Sharpness.FluxEdgeCopy.Copy
                      (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
                witness m) =
              (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
            Function.Injective profileRoute ∧
              (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                ∀ hm : m ∈ Ωactive,
                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                    β n v
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                    e0 m ≤
                    (β / 6) *
                      Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (Sharpness.ofEdgeFun
                          (FK.boxGraph 3 (2 * n))
                          (profileRoute ⟨m, hm⟩))) ∧
                ((∃ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                    ∃ hm : m ∈ Ωactive,
                      profileRoute ⟨m, hm⟩ ∉ Ωactive) ∨
                  ((∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                      ∀ _hm : m ∈ Ωactive,
                        ∃ m' :
                          {m :
                            ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                            m ∈ Ωactive},
                            profileRoute m' = m) ∧
                    (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                      ∀ hm : m ∈ Ωactive,
                        profileRoute ⟨m, hm⟩ ≠ m) ∧
                    (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                      ∀ _hm : m ∈ Ωactive,
                        ∃ m' :
                          {m :
                            ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                            m ∈ Ωactive},
                            m'.1 ≠ m ∧ profileRoute m' = m))) := by
  classical
  rcases hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty with
    ⟨profileRoute, witness, hleft, hright, hinj, hpoint⟩
  refine
    ⟨profileRoute, witness, hleft, hright, hinj, hpoint, ?_⟩
  exact
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_external_or_internal_cycle_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint hinj

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_external_or_internal_cycle
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hnonempty : Ωactive.Nonempty) :
    ∃ profileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      ∃ witness :
          (m :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive}) →
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) (profileRoute m)),
        (∀ m,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (FK.boxGraph 3 (2 * n)) (profileRoute m))
            (witness m) =
            doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) ∧
          (∀ m,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (FK.boxGraph 3 (2 * n)) (profileRoute m))
              ((Finset.univ :
                  Finset
                    (Sharpness.FluxEdgeCopy.Copy
                      (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
                witness m) =
              doubledBoxInnerPairSource n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) ∧
            Function.Injective profileRoute ∧
              (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                ∀ hm : m ∈ Ωactive,
                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                    β n v
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                    e0 m ≤
                    (β / 6) *
                      Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (Sharpness.ofEdgeFun
                          (FK.boxGraph 3 (2 * n))
                          (profileRoute ⟨m, hm⟩))) ∧
                ((∃ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                    ∃ hm : m ∈ Ωactive,
                      profileRoute ⟨m, hm⟩ ∉ Ωactive) ∨
                  ((∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                      ∀ _hm : m ∈ Ωactive,
                        ∃ m' :
                          {m :
                            ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                            m ∈ Ωactive},
                            profileRoute m' = m) ∧
                    (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                      ∀ hm : m ∈ Ωactive,
                        profileRoute ⟨m, hm⟩ ≠ m) ∧
                    (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                      ∀ _hm : m ∈ Ωactive,
                        ∃ m' :
                          {m :
                            ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                            m ∈ Ωactive},
                            m'.1 ≠ m ∧ profileRoute m' = m))) := by
  classical
  rcases hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty with
    ⟨profileRoute, witness, hleft, hright, hinj, hpoint⟩
  refine
    ⟨profileRoute, witness, hleft, hright, hinj, hpoint, ?_⟩
  exact
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_external_or_internal_cycle_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint hinj

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_singleton_external
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm : m ∈ Ωactive)
    (hsingleton : Ωactive = {m}) :
    ∃ profileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      ∃ _witness :
          (m :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive}) →
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) (profileRoute m)),
        profileRoute ⟨m, hm⟩ ∉ Ωactive := by
  classical
  have hnonempty : Ωactive.Nonempty := ⟨m, hm⟩
  rcases hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty with
    ⟨profileRoute, witness, hleft, hright, _hinj, hpoint⟩
  refine ⟨profileRoute, witness, ?_⟩
  exact
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_singleton_profileRoute_not_mem_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint m hm hsingleton

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_pair_swap_or_external
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (m₁ m₂ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm₁ : m₁ ∈ Ωactive) (hm₂ : m₂ ∈ Ωactive)
    (hpair :
      Ωactive =
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))) :
    ∃ profileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      ∃ _witness :
          (m :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive}) →
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) (profileRoute m)),
        profileRoute ⟨m₁, hm₁⟩ ∉ Ωactive ∨
          profileRoute ⟨m₂, hm₂⟩ ∉ Ωactive ∨
            (profileRoute ⟨m₁, hm₁⟩ = m₂ ∧
              profileRoute ⟨m₂, hm₂⟩ = m₁) := by
  classical
  have hnonempty : Ωactive.Nonempty := ⟨m₁, hm₁⟩
  rcases hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty with
    ⟨profileRoute, witness, hleft, hright, _hinj, hpoint⟩
  refine ⟨profileRoute, witness, ?_⟩
  exact
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_pair_swap_or_external_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint m₁ m₂ hm₁ hm₂ hpair

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_singleton_external
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm : m ∈ Ωactive)
    (hsingleton : Ωactive = {m}) :
    ∃ profileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      ∃ _witness :
          (m :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive}) →
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) (profileRoute m)),
        profileRoute ⟨m, hm⟩ ∉ Ωactive := by
  classical
  have hnonempty : Ωactive.Nonempty := ⟨m, hm⟩
  rcases hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty with
    ⟨profileRoute, witness, hleft, hright, _hinj, hpoint⟩
  refine ⟨profileRoute, witness, ?_⟩
  exact
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_singleton_profileRoute_not_mem_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint m hm hsingleton

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_pair_swap_or_external
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (m₁ m₂ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm₁ : m₁ ∈ Ωactive) (hm₂ : m₂ ∈ Ωactive)
    (hpair :
      Ωactive =
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))) :
    ∃ profileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      ∃ _witness :
          (m :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive}) →
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) (profileRoute m)),
        profileRoute ⟨m₁, hm₁⟩ ∉ Ωactive ∨
          profileRoute ⟨m₂, hm₂⟩ ∉ Ωactive ∨
            (profileRoute ⟨m₁, hm₁⟩ = m₂ ∧
              profileRoute ⟨m₂, hm₂⟩ = m₁) := by
  classical
  have hnonempty : Ωactive.Nonempty := ⟨m₁, hm₁⟩
  rcases hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty with
    ⟨profileRoute, witness, hleft, hright, _hinj, hpoint⟩
  refine ⟨profileRoute, witness, ?_⟩
  exact
    doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_pair_swap_or_external_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge hrows hleft hright hpoint m₁ m₂ hm₁ hm₂ hpair

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundsAt_exists_routes_singleton_external
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundsAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm : m ∈ Ωactive)
    (hsingleton : Ωactive = {m}) :
    ∃ emptyProfileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      ∃ _emptyWitness :
          (m :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive}) →
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) (emptyProfileRoute m)),
        ∃ innerProfileRoute :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive} →
              ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∃ _innerWitness :
              (m :
                {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                  m ∈ Ωactive}) →
                Finset
                  (Sharpness.FluxEdgeCopy.Copy
                    (FK.boxGraph 3 (2 * n)) (innerProfileRoute m)),
            emptyProfileRoute ⟨m, hm⟩ ∉ Ωactive ∧
              innerProfileRoute ⟨m, hm⟩ ∉ Ωactive := by
  classical
  rcases
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_singleton_external
        (β := β) hβpos (n := n) hcase.1 hvwedge hlt hypos
        (e0 := e0) hedge hrows m hm hsingleton with
    ⟨emptyProfileRoute, emptyWitness, hemptyExternal⟩
  rcases
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_singleton_external
        (β := β) hβpos (n := n) hcase.2 hvwedge hlt hypos
        (e0 := e0) hedge hrows m hm hsingleton with
    ⟨innerProfileRoute, innerWitness, hinnerExternal⟩
  exact
    ⟨emptyProfileRoute, emptyWitness, innerProfileRoute, innerWitness,
      hemptyExternal, hinnerExternal⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundsAt_exists_routes_pair_swap_or_external
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundsAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (m₁ m₂ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm₁ : m₁ ∈ Ωactive) (hm₂ : m₂ ∈ Ωactive)
    (hpair :
      Ωactive =
        ({m₁, m₂} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))) :
    ∃ emptyProfileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      ∃ _emptyWitness :
          (m :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive}) →
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) (emptyProfileRoute m)),
        ∃ innerProfileRoute :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive} →
              ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∃ _innerWitness :
              (m :
                {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                  m ∈ Ωactive}) →
                Finset
                  (Sharpness.FluxEdgeCopy.Copy
                    (FK.boxGraph 3 (2 * n)) (innerProfileRoute m)),
            (emptyProfileRoute ⟨m₁, hm₁⟩ ∉ Ωactive ∨
              emptyProfileRoute ⟨m₂, hm₂⟩ ∉ Ωactive ∨
                (emptyProfileRoute ⟨m₁, hm₁⟩ = m₂ ∧
                  emptyProfileRoute ⟨m₂, hm₂⟩ = m₁)) ∧
              (innerProfileRoute ⟨m₁, hm₁⟩ ∉ Ωactive ∨
                innerProfileRoute ⟨m₂, hm₂⟩ ∉ Ωactive ∨
                  (innerProfileRoute ⟨m₁, hm₁⟩ = m₂ ∧
                    innerProfileRoute ⟨m₂, hm₂⟩ = m₁)) := by
  classical
  rcases
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_pair_swap_or_external
        (β := β) hβpos (n := n) hcase.1 hvwedge hlt hypos
        (e0 := e0) hedge hrows m₁ m₂ hm₁ hm₂ hpair with
    ⟨emptyProfileRoute, emptyWitness, hemptySplit⟩
  rcases
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_pair_swap_or_external
        (β := β) hβpos (n := n) hcase.2 hvwedge hlt hypos
        (e0 := e0) hedge hrows m₁ m₂ hm₁ hm₂ hpair with
    ⟨innerProfileRoute, innerWitness, hinnerSplit⟩
  exact
    ⟨emptyProfileRoute, emptyWitness, innerProfileRoute, innerWitness,
      hemptySplit, hinnerSplit⟩

set_option linter.style.longLine false in


theorem
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_internal_injective_route_active_sum_le_weight_sum_of_pointwise
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hinj : Function.Injective profileRoute)
    (hinternal :
      ∀ m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
          profileRoute m ∈ Ωactive)
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
            β n v w e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩))) :
    (∑ m ∈ Ωactive,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m) ≤
      (β / 6) *
        ∑ m ∈ Ωactive,
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
  exact
    finsetSubtype_internal_injective_route_pointwise_mul_sum_le
      (Ω := Ωactive) (route := profileRoute) hinj hinternal
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m)
      (fun m =>
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
      (β / 6) hpoint

set_option linter.style.longLine false in


theorem
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_internal_injective_route_active_sum_le_weight_sum_of_pointwise
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hinj : Function.Injective profileRoute)
    (hinternal :
      ∀ m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
          profileRoute m ∈ Ωactive)
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v w e0 m ≤
            (β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (profileRoute ⟨m, hm⟩))) :
    (∑ m ∈ Ωactive,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m) ≤
      (β / 6) *
        ∑ m ∈ Ωactive,
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
  exact
    finsetSubtype_internal_injective_route_pointwise_mul_sum_le
      (Ω := Ωactive) (route := profileRoute) hinj hinternal
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m)
      (fun m =>
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
      (β / 6) hpoint

set_option linter.style.longLine false in


theorem
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_external_route_active_sum_le_external_image_weight_sum_of_pointwise
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hinj : Function.Injective profileRoute)
    (hpoint :
      ∀ m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
          profileRoute m ∉ Ωactive →
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
              β n v w e0 m.1 ≤
              (β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                    (profileRoute m))) :
    (∑ m ∈ Ωactive.attach.filter (fun m => profileRoute m ∉ Ωactive),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m.1) ≤
      (β / 6) *
        ∑ m ∈
          (Ωactive.attach.filter
            (fun m => profileRoute m ∉ Ωactive)).image profileRoute,
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
  exact
    finsetSubtype_external_route_pointwise_mul_sum_le_image_sum
      (Ω := Ωactive) (route := profileRoute) hinj
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m)
      (fun m =>
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
      (β / 6) hpoint

set_option linter.style.longLine false in

theorem
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_external_route_active_sum_le_external_image_weight_sum_of_pointwise
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {profileRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hinj : Function.Injective profileRoute)
    (hpoint :
      ∀ m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
          profileRoute m ∉ Ωactive →
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m.1 ≤
              (β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                    (profileRoute m))) :
    (∑ m ∈ Ωactive.attach.filter (fun m => profileRoute m ∉ Ωactive),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m.1) ≤
      (β / 6) *
        ∑ m ∈
          (Ωactive.attach.filter
            (fun m => profileRoute m ∉ Ωactive)).image profileRoute,
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
  exact
    finsetSubtype_external_route_pointwise_mul_sum_le_image_sum
      (Ω := Ωactive) (route := profileRoute) hinj
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m)
      (fun m =>
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
      (β / 6) hpoint

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_external_image_or_internal_active_sum_bound
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hnonempty : Ωactive.Nonempty) :
    ∃ profileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      ∃ witness :
          (m :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive}) →
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) (profileRoute m)),
        (∀ m,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (FK.boxGraph 3 (2 * n)) (profileRoute m))
            (witness m) =
            doubledBoxOriginToInnerEndpointSource n v) ∧
          (∀ m,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (FK.boxGraph 3 (2 * n)) (profileRoute m))
              ((Finset.univ :
                  Finset
                    (Sharpness.FluxEdgeCopy.Copy
                      (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
                witness m) =
              (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
            Function.Injective profileRoute ∧
              (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                ∀ hm : m ∈ Ωactive,
                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                    β n v
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                    e0 m ≤
                    (β / 6) *
                      Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (Sharpness.ofEdgeFun
                          (FK.boxGraph 3 (2 * n))
                          (profileRoute ⟨m, hm⟩))) ∧
                (((∃ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                    ∃ hm : m ∈ Ωactive,
                      profileRoute ⟨m, hm⟩ ∉ Ωactive) ∧
                  (∑ m ∈
                    Ωactive.attach.filter
                      (fun m => profileRoute m ∉ Ωactive),
                    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                      β n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                      e0 m.1) ≤
                    (β / 6) *
                      ∑ m ∈
                        (Ωactive.attach.filter
                          (fun m => profileRoute m ∉ Ωactive)).image
                            profileRoute,
                        Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                          (fun _ => 1)
                          (Sharpness.ofEdgeFun
                            (FK.boxGraph 3 (2 * n)) m)) ∨
                  ((∀ x :
                      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                        m ∈ Ωactive},
                        profileRoute x ∈ Ωactive) ∧
                    (((∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                        ∀ _hm : m ∈ Ωactive,
                          ∃ m' :
                            {m :
                              ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                              m ∈ Ωactive},
                              profileRoute m' = m) ∧
                      (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                        ∀ hm : m ∈ Ωactive,
                          profileRoute ⟨m, hm⟩ ≠ m) ∧
                      (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                        ∀ _hm : m ∈ Ωactive,
                          ∃ m' :
                            {m :
                              ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                              m ∈ Ωactive},
                              m'.1 ≠ m ∧ profileRoute m' = m)) ∧
                    (∑ m ∈ Ωactive,
                      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                        β n v
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                        e0 m) ≤
                      (β / 6) *
                        ∑ m ∈ Ωactive,
                          Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                            (fun _ => 1)
                            (Sharpness.ofEdgeFun
                              (FK.boxGraph 3 (2 * n)) m)))) := by
  classical
  rcases hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty with
    ⟨profileRoute, witness, hleft, hright, hinj, hpoint⟩
  have hexternalBound :
      (∑ m ∈
        Ωactive.attach.filter (fun m => profileRoute m ∉ Ωactive),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          e0 m.1) ≤
        (β / 6) *
          ∑ m ∈
            (Ωactive.attach.filter
              (fun m => profileRoute m ∉ Ωactive)).image profileRoute,
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
    exact
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_external_route_active_sum_le_external_image_weight_sum_of_pointwise
        (β := β) (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        (e0 := e0) (Ωactive := Ωactive) (profileRoute := profileRoute)
        hinj (fun m _hmext => hpoint m.1 m.2)
  refine ⟨profileRoute, witness, hleft, hright, hinj, hpoint, ?_⟩
  by_cases hinternal :
      ∀ x :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive},
          profileRoute x ∈ Ωactive
  · right
    have hperm :=
      doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetRoute_internal_injective_surjective_and_noFixed_of_strictSectorYPredecessor3
        (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) hedge hrows hleft hright hpoint hinj hinternal
    have hdistinct :
        ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                m ∈ Ωactive},
                m'.1 ≠ m ∧ profileRoute m' = m := by
      intro m hm
      exact
        finsetSubtype_internal_injective_fixedPointFree_route_distinct_predecessor
          (Ω := Ωactive) (route := profileRoute) hinj hinternal
          hperm.2 m hm
    have hsum :
        (∑ m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m) ≤
          (β / 6) *
            ∑ m ∈ Ωactive,
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
      exact
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_internal_injective_route_active_sum_le_weight_sum_of_pointwise
          (β := β) (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          (e0 := e0) (Ωactive := Ωactive) (profileRoute := profileRoute)
          hinj hinternal hpoint
    exact ⟨hinternal, ⟨⟨hperm.1, hperm.2, hdistinct⟩, hsum⟩⟩
  · left
    have hexternal :
        ∃ x :
          {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
            m ∈ Ωactive},
            profileRoute x ∉ Ωactive := by
      simpa using (not_forall.mp hinternal)
    rcases hexternal with ⟨m, hmext⟩
    exact ⟨⟨m.1, m.2, hmext⟩, hexternalBound⟩

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_route_external_image_or_internal_active_sum_bound
    {β : ℝ} {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hnonempty : Ωactive.Nonempty) :
    ∃ profileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      ∃ witness :
          (m :
            {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
              m ∈ Ωactive}) →
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) (profileRoute m)),
        (∀ m,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (FK.boxGraph 3 (2 * n)) (profileRoute m))
            (witness m) =
            doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) ∧
          (∀ m,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (FK.boxGraph 3 (2 * n)) (profileRoute m))
              ((Finset.univ :
                  Finset
                    (Sharpness.FluxEdgeCopy.Copy
                      (FK.boxGraph 3 (2 * n)) (profileRoute m))) \
                witness m) =
              doubledBoxInnerPairSource n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) ∧
            Function.Injective profileRoute ∧
              (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                ∀ hm : m ∈ Ωactive,
                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                    β n v
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                    e0 m ≤
                    (β / 6) *
                      Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (Sharpness.ofEdgeFun
                          (FK.boxGraph 3 (2 * n))
                          (profileRoute ⟨m, hm⟩))) ∧
                (((∃ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                    ∃ hm : m ∈ Ωactive,
                      profileRoute ⟨m, hm⟩ ∉ Ωactive) ∧
                  (∑ m ∈
                    Ωactive.attach.filter
                      (fun m => profileRoute m ∉ Ωactive),
                    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                      β n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                      e0 m.1) ≤
                    (β / 6) *
                      ∑ m ∈
                        (Ωactive.attach.filter
                          (fun m => profileRoute m ∉ Ωactive)).image
                            profileRoute,
                        Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                          (fun _ => 1)
                          (Sharpness.ofEdgeFun
                            (FK.boxGraph 3 (2 * n)) m)) ∨
                  ((∀ x :
                      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                        m ∈ Ωactive},
                        profileRoute x ∈ Ωactive) ∧
                    (∑ m ∈ Ωactive,
                      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                        β n v
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                        e0 m) ≤
                      (β / 6) *
                        ∑ m ∈ Ωactive,
                          Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                            (fun _ => 1)
                            (Sharpness.ofEdgeFun
                              (FK.boxGraph 3 (2 * n)) m))) := by
  classical
  rcases hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty with
    ⟨profileRoute, witness, hleft, hright, hinj, hpoint⟩
  have hexternalBound :
      (∑ m ∈
        Ωactive.attach.filter (fun m => profileRoute m ∉ Ωactive),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          e0 m.1) ≤
        (β / 6) *
          ∑ m ∈
            (Ωactive.attach.filter
              (fun m => profileRoute m ∉ Ωactive)).image profileRoute,
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
    exact
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_external_route_active_sum_le_external_image_weight_sum_of_pointwise
        (β := β) (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        (e0 := e0) (Ωactive := Ωactive) (profileRoute := profileRoute)
        hinj (fun m _hmext => hpoint m.1 m.2)
  refine ⟨profileRoute, witness, hleft, hright, hinj, hpoint, ?_⟩
  by_cases hinternal :
      ∀ x :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive},
          profileRoute x ∈ Ωactive
  · right
    have hsum :
        (∑ m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m) ≤
          (β / 6) *
            ∑ m ∈ Ωactive,
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
      exact
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_internal_injective_route_active_sum_le_weight_sum_of_pointwise
          (β := β) (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          (e0 := e0) (Ωactive := Ωactive) (profileRoute := profileRoute)
          hinj hinternal hpoint
    exact ⟨hinternal, hsum⟩
  · left
    have hexternal :
        ∃ x :
          {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
            m ∈ Ωactive},
            profileRoute x ∉ Ωactive := by
      simpa using (not_forall.mp hinternal)
    rcases hexternal with ⟨m, hmext⟩
    exact ⟨⟨m.1, m.2, hmext⟩, hexternalBound⟩

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt_exists_profileRoute_external_image_or_internal_cycle_active_sum_bound
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n)
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {Ωactive : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hrows :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ _hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hnonempty : Ωactive.Nonempty) :
    ∃ profileRoute :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive} →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      Function.Injective profileRoute ∧
        (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ hm : m ∈ Ωactive,
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
              (β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1)
                  (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                    (profileRoute ⟨m, hm⟩))) ∧
          (((∃ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
              ∃ hm : m ∈ Ωactive,
                profileRoute ⟨m, hm⟩ ∉ Ωactive) ∧
            (∑ m ∈
              Ωactive.attach.filter (fun m => profileRoute m ∉ Ωactive),
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0 m.1) ≤
              (β / 6) *
                ∑ m ∈
                  (Ωactive.attach.filter
                    (fun m => profileRoute m ∉ Ωactive)).image profileRoute,
                  Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) ∨
            ((∀ x :
                {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                  m ∈ Ωactive},
                  profileRoute x ∈ Ωactive) ∧
              (((∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                  ∀ _hm : m ∈ Ωactive,
                    ∃ m' :
                      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                        m ∈ Ωactive},
                        profileRoute m' = m) ∧
                (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                  ∀ hm : m ∈ Ωactive,
                    profileRoute ⟨m, hm⟩ ≠ m) ∧
                (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                  ∀ _hm : m ∈ Ωactive,
                    ∃ m' :
                      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                        m ∈ Ωactive},
                        m'.1 ≠ m ∧ profileRoute m' = m)) ∧
              (∑ m ∈ Ωactive,
                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                  β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                  e0 m) ≤
                (β / 6) *
                  ∑ m ∈ Ωactive,
                    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                      (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)))) := by
  classical
  rcases hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty with
    ⟨profileRoute, witness, hleft, hright, hinj, hpoint⟩
  have hexternalBound :
      (∑ m ∈
        Ωactive.attach.filter (fun m => profileRoute m ∉ Ωactive),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          e0 m.1) ≤
        (β / 6) *
          ∑ m ∈
            (Ωactive.attach.filter
              (fun m => profileRoute m ∉ Ωactive)).image profileRoute,
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
    exact
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_external_route_active_sum_le_external_image_weight_sum_of_pointwise
        (β := β) (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        (e0 := e0) (Ωactive := Ωactive) (profileRoute := profileRoute)
        hinj (fun m _hmext => hpoint m.1 m.2)
  refine ⟨profileRoute, hinj, hpoint, ?_⟩
  by_cases hinternal :
      ∀ x :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
          m ∈ Ωactive},
          profileRoute x ∈ Ωactive
  · right
    have hsurj :
        ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ _hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                m ∈ Ωactive},
                profileRoute m' = m := by
      intro m hm
      exact
        finsetSubtype_internal_injective_route_surjective
          (Ω := Ωactive) (route := profileRoute) hinj hinternal m hm
    have hnofixed :
        ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ hm : m ∈ Ωactive,
            profileRoute ⟨m, hm⟩ ≠ m := by
      intro m hm
      exact
        doubledBoxIncrementedFullSourceActive_innerPairSourceEquationActiveSetRoute_profileRoute_ne_self_of_strictSectorYPredecessor3
          (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
          (e0 := e0) hedge hrows hleft hright hpoint m hm
    have hdistinct :
        ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                m ∈ Ωactive},
                m'.1 ≠ m ∧ profileRoute m' = m := by
      intro m hm
      exact
        finsetSubtype_internal_injective_fixedPointFree_route_distinct_predecessor
          (Ω := Ωactive) (route := profileRoute) hinj hinternal
          hnofixed m hm
    have hsum :
        (∑ m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m) ≤
          (β / 6) *
            ∑ m ∈ Ωactive,
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
      exact
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_internal_injective_route_active_sum_le_weight_sum_of_pointwise
          (β := β) (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          (e0 := e0) (Ωactive := Ωactive) (profileRoute := profileRoute)
          hinj hinternal hpoint
    exact ⟨hinternal, ⟨⟨hsurj, hnofixed, hdistinct⟩, hsum⟩⟩
  · left
    have hexternal :
        ∃ x :
          {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
            m ∈ Ωactive},
            profileRoute x ∉ Ωactive := by
      simpa using (not_forall.mp hinternal)
    rcases hexternal with ⟨m, hmext⟩
    exact ⟨⟨m.1, m.2, hmext⟩, hexternalBound⟩

end Exact3D
end StatMech
