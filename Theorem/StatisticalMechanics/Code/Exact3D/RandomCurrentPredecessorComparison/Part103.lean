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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part95
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt_of_activeSetSplitSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSplitSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hcase ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  have hrows :
      ∀ m : Profile,
        ∀ hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n w e0 m := by
    intro m hm
    exact (Finset.mem_filter.mp (by simpa [Ωactive] using hm)).2
  by_cases hnonempty : Ωactive.Nonempty
  · exact hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty
  · let Split := Empty
    let split : {m : Profile // m ∈ Ωactive} → Finset Split :=
      fun _ => ∅
    let profileRoute :
        (m : {m : Profile // m ∈ Ωactive}) → Split → Profile :=
      fun _ i => nomatch i
    let witness :
        (m : {m : Profile // m ∈ Ωactive}) → (i : Split) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m i)) :=
      fun _ i => nomatch i
    refine ⟨Split, split, profileRoute, witness, ?_, ?_, ?_, ?_⟩
    · intro m i
      cases i
    · intro m i
      cases i
    · intro p _hp _q _hq _hroute
      cases p.2
    · intro m hm
      exact False.elim (hnonempty ⟨m, hm⟩)

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt_of_activeSetSplitSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSplitSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hcase ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  have hrows :
      ∀ m : Profile,
        ∀ hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n w e0 m := by
    intro m hm
    exact (Finset.mem_filter.mp (by simpa [Ωactive] using hm)).2
  by_cases hnonempty : Ωactive.Nonempty
  · exact hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty
  · let Split := Empty
    let split : {m : Profile // m ∈ Ωactive} → Finset Split :=
      fun _ => ∅
    let profileRoute :
        (m : {m : Profile // m ∈ Ωactive}) → Split → Profile :=
      fun _ i => nomatch i
    let witness :
        (m : {m : Profile // m ∈ Ωactive}) → (i : Split) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute m i)) :=
      fun _ i => nomatch i
    refine ⟨Split, split, profileRoute, witness, ?_, ?_, ?_, ?_⟩
    · intro m i
      cases i
    · intro m i
      cases i
    · intro p _hp _q _hq _hroute
      cases p.2
    · intro m hm
      exact False.elim (hnonempty ⟨m, hm⟩)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundsAt_of_activeSetSplitSubrouteChargeBoundsAt
    {β : ℝ} {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSplitSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt_of_activeSetSplitSubrouteChargeBoundAt
      hcase.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt_of_activeSetSplitSubrouteChargeBoundAt
      hcase.2⟩

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_emptySourceEquationSplitRoute_singleton_profileRoute_ne_self_of_strictSectorYPredecessor3
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
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {Split : Type}
    {splitRow : Finset Split}
    {profileRoute : Split → ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (i : Split) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
            (profileRoute i))}
    (hleft :
      ∀ i,
        Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
              (profileRoute i))
            (witness i) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ i,
        Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
              (profileRoute i))
            ((Finset.univ :
                Finset
                  (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                    (profileRoute i))) \
              witness i) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
        ∑ i ∈ splitRow,
          (β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) (profileRoute i)))
    {i0 : Split}
    (hsplit : splitRow = {i0}) :
    profileRoute i0 ≠ m := by
  intro hprofile
  have hpoint_single :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
        (β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (profileRoute i0)) := by
    simpa [hsplit] using hpoint
  exact
    doubledBoxIncrementedFullSourceActive_sameProfileSourceEquationRoute_not_pointwise_div_six_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) (m := m) (profile := profileRoute i0) (witness i0)
      hedge hactive hprofile (hleft i0) (hright i0) hpoint_single

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetSplitRoute_singleton_profileRoute_ne_self_of_strictSectorYPredecessor3
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
    {Split : Type}
    {split :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        Finset Split}
    {profileRoute :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
        Split → ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
        (i : Split) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
              (profileRoute m i))}
    (hleft :
      ∀ m i,
        Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
              (profileRoute m i))
            (witness m i) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ m i,
        Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
              (profileRoute m i))
            ((Finset.univ :
                Finset
                  (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                    (profileRoute m i))) \
              witness m i) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ∑ i ∈ split ⟨m, hm⟩,
              (β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                    (profileRoute ⟨m, hm⟩ i)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hm : m ∈ Ωactive) {i0 : Split}
    (hsplit : split ⟨m, hm⟩ = {i0}) :
    profileRoute ⟨m, hm⟩ i0 ≠ m := by
  exact
    doubledBoxIncrementedFullSourceActive_emptySourceEquationSplitRoute_singleton_profileRoute_ne_self_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) hedge (hrows m hm)
      (splitRow := split ⟨m, hm⟩)
      (profileRoute := profileRoute ⟨m, hm⟩)
      (witness := witness ⟨m, hm⟩)
      (fun i => hleft ⟨m, hm⟩ i) (fun i => hright ⟨m, hm⟩ i)
      (hpoint m hm) hsplit

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetSplitRoute_singletonFibers_external_or_internal_cycle_of_strictSectorYPredecessor3
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
    {Split : Type}
    {split :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        Finset Split}
    {label :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        Split}
    {profileRoute :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
        Split → ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {witness :
      (m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive}) →
        (i : Split) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
              (profileRoute m i))}
    (hleft :
      ∀ m i,
        Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
              (profileRoute m i))
            (witness m i) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ m i,
        Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
              (profileRoute m i))
            ((Finset.univ :
                Finset
                  (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                    (profileRoute m i))) \
              witness m i) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hinj :
      Set.InjOn
        (fun p :
            Sigma
              (fun _ :
                {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                  m ∈ Ωactive} => Split) =>
          profileRoute p.1 p.2)
        (Ωactive.attach.sigma split))
    (hpoint :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ∑ i ∈ split ⟨m, hm⟩,
              (β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                    (profileRoute ⟨m, hm⟩ i)))
    (hsplit :
      ∀ m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
          split m = {label m}) :
    (∃ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∃ hm : m ∈ Ωactive,
          profileRoute ⟨m, hm⟩ (label ⟨m, hm⟩) ∉ Ωactive) ∨
      ((∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ _hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                profileRoute m' (label m') = m) ∧
        (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ hm : m ∈ Ωactive,
            profileRoute ⟨m, hm⟩ (label ⟨m, hm⟩) ≠ m) ∧
        (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ _hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                m'.1 ≠ m ∧ profileRoute m' (label m') = m)) := by
  let singleRoute :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    fun m => profileRoute m (label m)
  have hinjSingle : Function.Injective singleRoute := by
    simpa [singleRoute] using
      finset_attach_sigma_singleton_route_injective_of_injOn
        (s := Ωactive) (split := split) (label := label)
        (route := profileRoute) hinj hsplit
  have hnofixed :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ hm : m ∈ Ωactive,
          singleRoute ⟨m, hm⟩ ≠ m := by
    intro m hm
    simpa [singleRoute] using
      doubledBoxIncrementedFullSourceActive_emptySourceEquationActiveSetSplitRoute_singleton_profileRoute_ne_self_of_strictSectorYPredecessor3
        (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) hedge hrows hleft hright hpoint m hm
        (hsplit ⟨m, hm⟩)
  by_cases hinternal :
      ∀ m :
        {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
          singleRoute m ∈ Ωactive
  · right
    have hsurj :
        ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ _hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                singleRoute m' = m := by
      intro m hm
      exact
        finsetSubtype_internal_injective_route_surjective
          (Ω := Ωactive) (route := singleRoute) hinjSingle hinternal m hm
    have hdistinct :
        ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          ∀ _hm : m ∈ Ωactive,
            ∃ m' :
              {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
                m'.1 ≠ m ∧ singleRoute m' = m := by
      intro m hm
      exact
        finsetSubtype_internal_injective_fixedPointFree_route_distinct_predecessor
          (Ω := Ωactive) (route := singleRoute) hinjSingle hinternal
          hnofixed m hm
    constructor
    · intro m hm
      rcases hsurj m hm with ⟨m', hm'⟩
      exact ⟨m', by simpa [singleRoute] using hm'⟩
    constructor
    · intro m hm
      simpa [singleRoute] using hnofixed m hm
    · intro m hm
      rcases hdistinct m hm with ⟨m', hne, hm'⟩
      exact ⟨m', hne, by simpa [singleRoute] using hm'⟩
  · left
    have hexternal :
        ∃ m :
          {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ Ωactive},
            singleRoute m ∉ Ωactive := by
      simpa using (not_forall.mp hinternal)
    rcases hexternal with ⟨m, hmext⟩
    exact ⟨m.1, m.2, by simpa [singleRoute] using hmext⟩

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hsourceEq :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hsourceEq v hvwedge hlt hypos e0 hedge Ω with
    ⟨Split, split, profileRoute, witness, hleft, hright, hinj, hpoint⟩
  refine ⟨Split, split, profileRoute, witness, ?_, hinj, hpoint⟩
  intro m i
  rw [edgeCopySourcePairWitnesses_mem]
  exact ⟨hleft m i, hright m i⟩

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hsourceEq :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hsourceEq v hvwedge hlt hypos e0 hedge Ω with
    ⟨Split, split, profileRoute, witness, hleft, hright, hinj, hpoint⟩
  refine ⟨Split, split, profileRoute, witness, ?_, hinj, hpoint⟩
  intro m i
  rw [edgeCopySourcePairWitnesses_mem]
  exact ⟨hleft m i, hright m i⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundsAt
    {β : ℝ} {n : ℕ}
    (hsourceEq :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
      hsourceEq.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
      hsourceEq.2⟩

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hprofileWitness :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hprofileWitness ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  rcases hprofileWitness v hvwedge hlt hypos e0 hedge Ω with
    ⟨Split, split, profileRoute, witness, hwitness, hinj, hpoint⟩
  have hpoint' :
      ∀ a : {m : Profile // m ∈ Ωactive},
        F a.1 ≤
          ∑ i ∈ split a,
            (β / 6) *
              Sharpness.weight G β (fun _ => (1 : ℝ))
                (Sharpness.ofEdgeFun G (profileRoute a i)) := by
    intro a
    simpa [F, G, Ωactive, w] using hpoint a.1 a.2
  rcases
      edgeCopySourcePairData_attach_splitRoutes_of_profileWitness_routes
        (G := G) (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
        Ωactive F split profileRoute witness hwitness hinj hpoint' with
    ⟨route, hinjData, hpointData⟩
  refine ⟨Split, split, route, hinjData, ?_⟩
  intro m hm
  simpa [F, G, Ωactive, w] using hpointData m hm

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hprofileWitness :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hprofileWitness ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hprofileWitness v hvwedge hlt hypos e0 hedge Ω with
    ⟨Split, split, profileRoute, witness, hwitness, hinj, hpoint⟩
  have hpoint' :
      ∀ a : {m : Profile // m ∈ Ωactive},
        F a.1 ≤
          ∑ i ∈ split a,
            (β / 6) *
              Sharpness.weight G β (fun _ => (1 : ℝ))
                (Sharpness.ofEdgeFun G (profileRoute a i)) := by
    intro a
    simpa [F, G, Ωactive, w] using hpoint a.1 a.2
  rcases
      edgeCopySourcePairData_attach_splitRoutes_of_profileWitness_routes
        (G := G) (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
        Ωactive F split profileRoute witness hwitness hinj hpoint' with
    ⟨route, hinjData, hpointData⟩
  refine ⟨Split, split, route, hinjData, ?_⟩
  intro m hm
  simpa [F, G, Ωactive, w] using hpointData m hm

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundsAt
    {β : ℝ} {n : ℕ}
    (hprofileWitness :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
      hprofileWitness.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
      hprofileWitness.2⟩

end Exact3D
end StatMech
