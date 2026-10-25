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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part39
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairData_doubledBoxOriginIncidentSupportPattern_routes_of_profileWitness_singleton_multi_checks
    {β c : ℝ} {n : ℕ}
    {A B : Finset (FK.boxVerts 3 (2 * n))}
    (Ωactive :
      Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (profileRoute :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (witness :
      (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) →
        (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute S m)))
    (hwitness :
      ∀ S m,
        witness S m ∈
          edgeCopySourcePairWitnesses
            (FK.boxGraph 3 (2 * n)) A B (profileRoute S m))
    (hsingle :
      ∀ S ∈
          Finset.filter (fun S => S.Nonempty)
            (Finset.powerset (doubledBoxOriginIncidentEdges n)),
        S.card = 1 →
          Set.InjOn (profileRoute S)
              (Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S)) ∧
            (∀ m ∈ Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              doubledBoxOriginIncidentSupport n (profileRoute S m) = S) ∧
              ∀ m ∈ Ωactive.filter
                  (fun m => doubledBoxOriginIncidentSupport n m = S),
                F m ≤
                  c * Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                    (fun _ => 1)
                    (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                      (profileRoute S m)))
    (hmulti :
      ∀ S ∈
          Finset.filter (fun S => S.Nonempty)
            (Finset.powerset (doubledBoxOriginIncidentEdges n)),
        1 < S.card →
          Set.InjOn (profileRoute S)
              (Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S)) ∧
            (∀ m ∈ Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              doubledBoxOriginIncidentSupport n (profileRoute S m) = S) ∧
              ∀ m ∈ Ωactive.filter
                  (fun m => doubledBoxOriginIncidentSupport n m = S),
                F m ≤
                  c * Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                    (fun _ => 1)
                    (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                      (profileRoute S m))) :
    ∃ route :
        Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
            edgeCopySourcePairData (FK.boxGraph 3 (2 * n)) A B,
      (∀ S ∈
          Finset.filter (fun S => S.Nonempty)
            (Finset.powerset (doubledBoxOriginIncidentEdges n)),
        Set.InjOn (route S)
          (Ωactive.filter
            (fun m => doubledBoxOriginIncidentSupport n m = S))) ∧
        (∀ S ∈
            Finset.filter (fun S => S.Nonempty)
              (Finset.powerset (doubledBoxOriginIncidentEdges n)),
          ∀ m ∈ Ωactive.filter
              (fun m => doubledBoxOriginIncidentSupport n m = S),
            doubledBoxOriginIncidentSupport n (route S m).1 = S) ∧
          ∀ S ∈
              Finset.filter (fun S => S.Nonempty)
                (Finset.powerset (doubledBoxOriginIncidentEdges n)),
            ∀ m ∈ Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              F m ≤
                c * edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (route S m) := by
  let supportPatterns :
      Finset (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  have hpatterns_nonempty : ∀ S ∈ supportPatterns, S.Nonempty := by
    intro S hS
    exact
      doubledBoxNonemptyOriginIncidentSupportPattern_nonempty_of_mem
        (n := n) (S := S) (by simpa [supportPatterns] using hS)
  simpa [supportPatterns] using
    edgeCopySourcePairData_supportPattern_routes_of_profileWitness_singleton_multi_checks
      (G := FK.boxGraph 3 (2 * n)) (A := A) (B := B)
      (β := β) (J := fun _ => (1 : ℝ)) (c := c)
      Ωactive supportPatterns (doubledBoxOriginIncidentSupport n) F
      hpatterns_nonempty profileRoute witness hwitness
      (by simpa [supportPatterns] using hsingle)
      (by simpa [supportPatterns] using hmulti)

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairData_doubledBoxOriginIncidentSupportPattern_routes_of_profileWitness_card_cases
    {β c : ℝ} {n : ℕ}
    {A B : Finset (FK.boxVerts 3 (2 * n))}
    (Ωactive :
      Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (profileRoute :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (witness :
      (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) →
        (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (profileRoute S m)))
    (hwitness :
      ∀ S m,
        witness S m ∈
          edgeCopySourcePairWitnesses
            (FK.boxGraph 3 (2 * n)) A B (profileRoute S m))
    (hcard1 :
      ∀ S ∈
          Finset.filter (fun S => S.Nonempty)
            (Finset.powerset (doubledBoxOriginIncidentEdges n)),
        S.card = 1 →
          DoubledBoxOriginIncidentSupportPatternProfileRouteChecks
            β c n Ωactive F profileRoute S)
    (hcard2 :
      ∀ S ∈
          Finset.filter (fun S => S.Nonempty)
            (Finset.powerset (doubledBoxOriginIncidentEdges n)),
        S.card = 2 →
          DoubledBoxOriginIncidentSupportPatternProfileRouteChecks
            β c n Ωactive F profileRoute S)
    (hcard3 :
      ∀ S ∈
          Finset.filter (fun S => S.Nonempty)
            (Finset.powerset (doubledBoxOriginIncidentEdges n)),
        S.card = 3 →
          DoubledBoxOriginIncidentSupportPatternProfileRouteChecks
            β c n Ωactive F profileRoute S)
    (hcard4 :
      ∀ S ∈
          Finset.filter (fun S => S.Nonempty)
            (Finset.powerset (doubledBoxOriginIncidentEdges n)),
        S.card = 4 →
          DoubledBoxOriginIncidentSupportPatternProfileRouteChecks
            β c n Ωactive F profileRoute S)
    (hcard5 :
      ∀ S ∈
          Finset.filter (fun S => S.Nonempty)
            (Finset.powerset (doubledBoxOriginIncidentEdges n)),
        S.card = 5 →
          DoubledBoxOriginIncidentSupportPatternProfileRouteChecks
            β c n Ωactive F profileRoute S)
    (hcard6 :
      ∀ S ∈
          Finset.filter (fun S => S.Nonempty)
            (Finset.powerset (doubledBoxOriginIncidentEdges n)),
        S.card = 6 →
          DoubledBoxOriginIncidentSupportPatternProfileRouteChecks
            β c n Ωactive F profileRoute S) :
    ∃ route :
        Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
            edgeCopySourcePairData (FK.boxGraph 3 (2 * n)) A B,
      (∀ S ∈
          Finset.filter (fun S => S.Nonempty)
            (Finset.powerset (doubledBoxOriginIncidentEdges n)),
        Set.InjOn (route S)
          (Ωactive.filter
            (fun m => doubledBoxOriginIncidentSupport n m = S))) ∧
        (∀ S ∈
            Finset.filter (fun S => S.Nonempty)
              (Finset.powerset (doubledBoxOriginIncidentEdges n)),
          ∀ m ∈ Ωactive.filter
              (fun m => doubledBoxOriginIncidentSupport n m = S),
            doubledBoxOriginIncidentSupport n (route S m).1 = S) ∧
          ∀ S ∈
              Finset.filter (fun S => S.Nonempty)
                (Finset.powerset (doubledBoxOriginIncidentEdges n)),
            ∀ m ∈ Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              F m ≤
                c * edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (route S m) := by
  refine
    edgeCopySourcePairData_doubledBoxOriginIncidentSupportPattern_routes_of_profileWitness_singleton_multi_checks
      (β := β) (c := c) (n := n) (A := A) (B := B)
      Ωactive F profileRoute witness hwitness ?_ ?_
  · intro S hS hcard
    simpa [DoubledBoxOriginIncidentSupportPatternProfileRouteChecks] using
      hcard1 S hS hcard
  · intro S hS hmulti
    rcases
        doubledBoxNonemptyOriginIncidentSupportPattern_multi_card_eq_two_or_three_or_four_or_five_or_six
          (n := n) (S := S) hS hmulti with
      hcard2S | hcard3S | hcard4S | hcard5S | hcard6S
    · simpa [DoubledBoxOriginIncidentSupportPatternProfileRouteChecks] using
        hcard2 S hS hcard2S
    · simpa [DoubledBoxOriginIncidentSupportPatternProfileRouteChecks] using
        hcard3 S hS hcard3S
    · simpa [DoubledBoxOriginIncidentSupportPatternProfileRouteChecks] using
        hcard4 S hS hcard4S
    · simpa [DoubledBoxOriginIncidentSupportPatternProfileRouteChecks] using
        hcard5 S hS hcard5S
    · simpa [DoubledBoxOriginIncidentSupportPatternProfileRouteChecks] using
        hcard6 S hS hcard6S

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupportPatterns_card_eq_64_of_pos
    {n : ℕ} (hn : 0 < n) :
    ((doubledBoxOriginIncidentEdges n).powerset).card = 64 := by
  rw [Finset.card_powerset, doubledBoxOriginIncidentEdges_card_eq_six_of_pos hn]
  norm_num

set_option linter.style.longLine false in


theorem doubledBoxNonemptyOriginIncidentSupportPatterns_card_le_64_of_pos
    {n : ℕ} (hn : 0 < n) :
    (((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty)).card ≤ 64 := by
  calc
    (((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty)).card ≤
        ((doubledBoxOriginIncidentEdges n).powerset).card :=
      Finset.card_filter_le _ _
    _ = 64 :=
      doubledBoxOriginIncidentSupportPatterns_card_eq_64_of_pos (n := n) hn

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupportPatterns_card_le_64 (n : ℕ) :
    ((doubledBoxOriginIncidentEdges n).powerset).card ≤ 64 := by
  rw [Finset.card_powerset]
  have hcard := doubledBoxOriginIncidentEdges_card_le_six n
  calc
    2 ^ (doubledBoxOriginIncidentEdges n).card ≤ 2 ^ 6 :=
      Nat.pow_le_pow_right (by norm_num) hcard
    _ = 64 := by norm_num

set_option linter.style.longLine false in


theorem doubledBoxNonemptyOriginIncidentSupportPatterns_card_le_64 (n : ℕ) :
    (((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty)).card ≤ 64 := by
  calc
    (((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty)).card ≤
        ((doubledBoxOriginIncidentEdges n).powerset).card :=
      Finset.card_filter_le _ _
    _ ≤ 64 := doubledBoxOriginIncidentSupportPatterns_card_le_64 n

set_option linter.style.longLine false in


theorem doubledBoxNonemptyOriginIncidentSupportPatterns_sum_le_of_forall_le_div_64
    {n : ℕ}
    {F : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℝ} {target : ℝ}
    (htarget : 0 ≤ target)
    (hF :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        F S ≤ target / 64) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty), F S) ≤ target := by
  classical
  let patterns : Finset (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
    ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty)
  have hcardNat : patterns.card ≤ 64 := by
    simpa [patterns] using
      doubledBoxNonemptyOriginIncidentSupportPatterns_card_le_64 n
  have hcard : (patterns.card : ℝ) ≤ 64 := by
    exact_mod_cast hcardNat
  have hshare_nonneg : 0 ≤ target / 64 := by
    nlinarith
  calc
    (∑ S ∈ patterns, F S) ≤ ∑ S ∈ patterns, target / 64 := by
      exact Finset.sum_le_sum (by simpa [patterns] using hF)
    _ = (patterns.card : ℝ) * (target / 64) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 64 * (target / 64) := by
      exact mul_le_mul_of_nonneg_right hcard hshare_nonneg
    _ = target := by ring

set_option linter.style.longLine false in


theorem doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
    {n : ℕ}
    {F :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℝ}
    {target : ℝ}
    (htarget : 0 ≤ target)
    (hF :
      ∀ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∀ ew ∈ S, F S ew ≤ target / 384) :
    (∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty),
      ∑ ew ∈ S, F S ew) ≤ target := by
  classical
  let patterns : Finset (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
    ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty)
  have hpatternCardNat : patterns.card ≤ 64 := by
    simpa [patterns] using
      doubledBoxNonemptyOriginIncidentSupportPatterns_card_le_64 n
  have hpatternCard : (patterns.card : ℝ) ≤ 64 := by
    exact_mod_cast hpatternCardNat
  have hshare_nonneg : 0 ≤ target / 384 := by nlinarith
  have howner_cap :
      ∀ S ∈ patterns, (S.card : ℝ) ≤ 6 := by
    intro S hS
    exact_mod_cast
      (doubledBoxNonemptyOriginIncidentSupportPattern_card_le_six
        (n := n) (S := S) (by simpa [patterns] using hS))
  calc
    (∑ S ∈ patterns, ∑ ew ∈ S, F S ew) ≤
        ∑ S ∈ patterns, ∑ _ew ∈ S, target / 384 := by
      refine Finset.sum_le_sum ?_
      intro S hS
      exact Finset.sum_le_sum (hF S (by simpa [patterns] using hS))
    _ = ∑ S ∈ patterns, (S.card : ℝ) * (target / 384) := by
      refine Finset.sum_congr rfl ?_
      intro S _hS
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _S ∈ patterns, 6 * (target / 384) := by
      refine Finset.sum_le_sum ?_
      intro S hS
      exact mul_le_mul_of_nonneg_right (howner_cap S hS) hshare_nonneg
    _ = (patterns.card : ℝ) * (6 * (target / 384)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 64 * (6 * (target / 384)) := by
      have hright_nonneg : 0 ≤ 6 * (target / 384) := by nlinarith
      exact mul_le_mul_of_nonneg_right hpatternCard hright_nonneg
    _ = target := by ring

set_option linter.style.longLine false in


theorem finset_sum_eq_sum_fiber_filter_of_mem
    {α ι : Type*} [DecidableEq ι] (Ω : Finset α) (S : Finset ι)
    (classOf : α → ι) (F : α → ℝ)
    (hmem : ∀ a ∈ Ω, classOf a ∈ S) :
    (∑ a ∈ Ω, F a) =
      ∑ i ∈ S, ∑ a ∈ Ω.filter (fun a => classOf a = i), F a := by
  have hpoint :
      ∀ a ∈ Ω, F a =
        ∑ i ∈ S, if classOf a = i then F a else 0 := by
    intro a ha
    have hsum :
        (∑ i ∈ S, if classOf a = i then F a else 0) = F a := by
      refine
        (Finset.sum_eq_single_of_mem
          (s := S)
          (f := fun i => if classOf a = i then F a else 0)
          (classOf a) (hmem a ha) ?_).trans ?_
      · intro i _hi hne
        have hnot : ¬ classOf a = i := by
          intro h
          exact hne h.symm
        simp [hnot]
      · simp
    exact hsum.symm
  calc
    (∑ a ∈ Ω, F a) =
        ∑ a ∈ Ω, ∑ i ∈ S, if classOf a = i then F a else 0 := by
      exact Finset.sum_congr rfl hpoint
    _ = ∑ i ∈ S, ∑ a ∈ Ω, if classOf a = i then F a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ S, ∑ a ∈ Ω.filter (fun a => classOf a = i), F a := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [Finset.sum_filter]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_finset_sum_eq_sum_supportPatternFilters
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ) :
    (∑ m ∈ Ω, F m) =
      ∑ S ∈ (doubledBoxOriginIncidentEdges n).powerset,
        ∑ m ∈ Ω.filter
          (fun m => doubledBoxOriginIncidentSupport n m = S),
          F m := by
  exact
    finset_sum_eq_sum_fiber_filter_of_mem Ω
      (doubledBoxOriginIncidentEdges n).powerset
      (doubledBoxOriginIncidentSupport n) F
      (fun _m _hm =>
        doubledBoxOriginIncidentSupport_mem_originIncidentEdges_powerset)

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_filter_eq_active_filter_of_nonempty
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hS : S.Nonempty) :
    Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S) =
      (Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m)).filter
        (fun m => doubledBoxOriginIncidentSupport n m = S) := by
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨hm.1, ?_⟩, hm.2⟩
    have hsupport_nonempty :
        (doubledBoxOriginIncidentSupport n m).Nonempty := by
      simpa [hm.2] using hS
    exact
      (doubledBoxOriginIncidentSupport_nonempty_iff_originTouchesEdgeSupport
        (n := n) (m := m)).1 hsupport_nonempty
  · intro hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_filter]
    exact ⟨hm.1.1, hm.2⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginTouchesEdgeSupport_filter_sum_eq_sum_nonempty_originIncidentSupportPatternFilters
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ) :
    (∑ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m), F m) =
      ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty),
        ∑ m ∈ Ω.filter
          (fun m => doubledBoxOriginIncidentSupport n m = S),
          F m := by
  let patterns :=
    ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty)
  have hmem :
      ∀ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        doubledBoxOriginIncidentSupport n m ∈ patterns := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_filter]
    exact
      ⟨doubledBoxOriginIncidentSupport_mem_originIncidentEdges_powerset,
        (doubledBoxOriginIncidentSupport_nonempty_iff_originTouchesEdgeSupport
          (n := n) (m := m)).2 hm.2⟩
  calc
    (∑ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m), F m) =
        ∑ S ∈ patterns,
          ∑ m ∈
            (Ω.filter
              (fun m => doubledBoxOriginTouchesEdgeSupport n m)).filter
              (fun m => doubledBoxOriginIncidentSupport n m = S),
            F m := by
      exact
        finset_sum_eq_sum_fiber_filter_of_mem
          (Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m))
          patterns (doubledBoxOriginIncidentSupport n) F hmem
    _ =
        ∑ S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
            (fun S => S.Nonempty),
          ∑ m ∈ Ω.filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
            F m := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      rw [Finset.mem_filter] at hS
      rw [
        ← doubledBoxOriginIncidentSupport_filter_eq_active_filter_of_nonempty
          (n := n) Ω hS.2]

end Exact3D
end StatMech
