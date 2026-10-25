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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part40
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

theorem doubledBoxOriginIncidentOwner_eq_none_iff_not_originTouchesEdgeSupport
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    doubledBoxOriginIncidentOwner n m = none ↔
      ¬ doubledBoxOriginTouchesEdgeSupport n m := by
  classical
  by_cases h : doubledBoxOriginTouchesEdgeSupport n m
  · simp [doubledBoxOriginIncidentOwner, h]
  · simp [doubledBoxOriginIncidentOwner, h]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_eq_none_iff_originIncidentMultiplicity_eq_zero
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    doubledBoxOriginIncidentOwner n m = none ↔
      doubledBoxOriginIncidentMultiplicity n m = 0 := by
  rw [doubledBoxOriginIncidentOwner_eq_none_iff_not_originTouchesEdgeSupport,
    not_doubledBoxOriginTouchesEdgeSupport_iff_originIncidentMultiplicity_eq_zero]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_spec_of_eq_some
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (howner : doubledBoxOriginIncidentOwner n m = some e) :
    e ∈ doubledBoxOriginIncidentEdges n ∧ m e ≠ 0 := by
  classical
  by_cases hactive : doubledBoxOriginTouchesEdgeSupport n m
  · let ew :=
      Classical.choose
        ((doubledBoxOriginTouchesEdgeSupport_iff_exists_originIncidentEdge
          (n := n) (m := m)).1 hactive)
    have hspec :
        ew ∈ doubledBoxOriginIncidentEdges n ∧ m ew ≠ 0 :=
      Classical.choose_spec
        ((doubledBoxOriginTouchesEdgeSupport_iff_exists_originIncidentEdge
          (n := n) (m := m)).1 hactive)
    have heq : ew = e := by
      exact
        Option.some.inj
          (by
            simpa [doubledBoxOriginIncidentOwner, hactive, ew] using howner)
    simpa [← heq] using hspec
  · simp [doubledBoxOriginIncidentOwner, hactive] at howner

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_exists_of_originTouchesEdgeSupport
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hactive : doubledBoxOriginTouchesEdgeSupport n m) :
    ∃ e ∈ doubledBoxOriginIncidentEdges n,
      doubledBoxOriginIncidentOwner n m = some e ∧ m e ≠ 0 := by
  classical
  let ew :=
    Classical.choose
      ((doubledBoxOriginTouchesEdgeSupport_iff_exists_originIncidentEdge
        (n := n) (m := m)).1 hactive)
  have hspec :
      ew ∈ doubledBoxOriginIncidentEdges n ∧ m ew ≠ 0 :=
    Classical.choose_spec
      ((doubledBoxOriginTouchesEdgeSupport_iff_exists_originIncidentEdge
        (n := n) (m := m)).1 hactive)
  refine ⟨ew, hspec.1, ?_, hspec.2⟩
  simp [doubledBoxOriginIncidentOwner, hactive, ew]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_eq_singleton_iff
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset} :
    doubledBoxOriginIncidentSupport n m = {ew} ↔
      ew ∈ doubledBoxOriginIncidentEdges n ∧ m ew ≠ 0 ∧
        ∀ e ∈ doubledBoxOriginIncidentEdges n, e ≠ ew → m e = 0 := by
  constructor
  · intro hsupport
    have hew_support : ew ∈ doubledBoxOriginIncidentSupport n m := by
      rw [hsupport]
      simp
    rcases mem_doubledBoxOriginIncidentSupport.mp hew_support with
      ⟨hew_origin, hew_pos⟩
    refine ⟨hew_origin, hew_pos, ?_⟩
    intro e heorigin hne
    by_contra hpos
    have hesupport : e ∈ doubledBoxOriginIncidentSupport n m :=
      mem_doubledBoxOriginIncidentSupport.mpr ⟨heorigin, hpos⟩
    have heq : e = ew := by
      have hsingleton :
          e ∈ ({ew} :
            Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) := by
        simpa [hsupport] using hesupport
      simpa using hsingleton
    exact hne heq
  · rintro ⟨hew_origin, hew_pos, hzero⟩
    ext e
    constructor
    · intro he
      rcases mem_doubledBoxOriginIncidentSupport.mp he with
        ⟨heorigin, hme⟩
      by_cases hew : e = ew
      · simp [hew]
      · exact False.elim (hme (hzero e heorigin hew))
    · intro he
      have heq : e = ew := by
        simpa using he
      rw [heq]
      exact
        mem_doubledBoxOriginIncidentSupport.mpr ⟨hew_origin, hew_pos⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_eq_singleton_of_mem_of_ne_zero_of_forall_ne_eq_zero
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew_origin : ew ∈ doubledBoxOriginIncidentEdges n)
    (hew_pos : m ew ≠ 0)
    (hzero :
      ∀ e ∈ doubledBoxOriginIncidentEdges n, e ≠ ew → m e = 0) :
    doubledBoxOriginIncidentSupport n m = {ew} :=
  doubledBoxOriginIncidentSupport_eq_singleton_iff.mpr
    ⟨hew_origin, hew_pos, hzero⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_eq_singleton_of_originIncidentOwner_eq_some_of_forall_ne_eq_zero
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (howner : doubledBoxOriginIncidentOwner n m = some ew)
    (hzero :
      ∀ e ∈ doubledBoxOriginIncidentEdges n, e ≠ ew → m e = 0) :
    doubledBoxOriginIncidentSupport n m = {ew} := by
  ext e
  constructor
  · intro he
    rcases (mem_doubledBoxOriginIncidentSupport.mp he) with ⟨heorigin, hme⟩
    by_cases hew : e = ew
    · simp [hew]
    · exact False.elim (hme (hzero e heorigin hew))
  · intro he
    have heq : e = ew := by
      simpa using he
    rw [heq]
    exact
      mem_doubledBoxOriginIncidentSupport.mpr
        (doubledBoxOriginIncidentOwner_spec_of_eq_some
          (n := n) (m := m) (e := ew) howner)

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_eq_some_of_originIncidentSupport_eq_singleton
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hsupport : doubledBoxOriginIncidentSupport n m = {ew}) :
    doubledBoxOriginIncidentOwner n m = some ew := by
  have hsupport_nonempty : (doubledBoxOriginIncidentSupport n m).Nonempty := by
    rw [hsupport]
    exact ⟨ew, by simp⟩
  have htouch : doubledBoxOriginTouchesEdgeSupport n m :=
    (doubledBoxOriginIncidentSupport_nonempty_iff_originTouchesEdgeSupport
      (n := n) (m := m)).1 hsupport_nonempty
  rcases doubledBoxOriginIncidentOwner_exists_of_originTouchesEdgeSupport
      (n := n) (m := m) htouch with
    ⟨e, heorigin, howner, hme⟩
  have hesupport : e ∈ doubledBoxOriginIncidentSupport n m :=
    mem_doubledBoxOriginIncidentSupport.mpr ⟨heorigin, hme⟩
  have heq : e = ew := by
    have hsingleton :
        e ∈ ({ew} :
          Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) := by
      simpa [hsupport] using hesupport
    simpa using hsingleton
  simpa [heq] using howner

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_singleton_filter_subset_originIncidentOwner_filter
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = {ew}) ⊆
      Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some ew) := by
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  exact
    ⟨hm.1,
      doubledBoxOriginIncidentOwner_eq_some_of_originIncidentSupport_eq_singleton
        (n := n) (m := m) (ew := ew) hm.2⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_singleton_filter_subset_multiplicity_filter
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = {ew}) ⊆
      Ω.filter (fun m => m ew ≠ 0) := by
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  refine ⟨hm.1, ?_⟩
  have hew_support : ew ∈ doubledBoxOriginIncidentSupport n m := by
    rw [hm.2]
    simp
  exact (mem_doubledBoxOriginIncidentSupport.mp hew_support).2

set_option linter.style.longLine false in

theorem doubledBoxOriginIncidentSupport_singleton_filter_card_le_originIncidentOwner_filter_card
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = {ew})).card ≤
      (Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some ew)).card :=
  Finset.card_le_card
    (doubledBoxOriginIncidentSupport_singleton_filter_subset_originIncidentOwner_filter
      (n := n) Ω ew)

set_option linter.style.longLine false in


theorem forall_originIncidentSupportSingletonRows_of_forall_originIncidentOwnerRows
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    {P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop}
    (hP :
      ∀ m ∈ Ω.filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew),
        P m) :
    ∀ m ∈ Ω.filter
        (fun m => doubledBoxOriginIncidentSupport n m = {ew}),
      P m := by
  intro m hm
  exact hP m
    (doubledBoxOriginIncidentSupport_singleton_filter_subset_originIncidentOwner_filter
      (n := n) Ω ew hm)

set_option linter.style.longLine false in


theorem forall_originIncidentSupportSingletonRows_of_forall_multiplicityRows
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    {P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop}
    (hP : ∀ m ∈ Ω.filter (fun m => m ew ≠ 0), P m) :
    ∀ m ∈ Ω.filter
        (fun m => doubledBoxOriginIncidentSupport n m = {ew}),
      P m := by
  intro m hm
  exact hP m
    (doubledBoxOriginIncidentSupport_singleton_filter_subset_multiplicity_filter
      (n := n) Ω ew hm)

set_option linter.style.longLine false in

theorem doubledBoxOriginTouchesEdgeSupport_of_originIncidentOwner_eq_some
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (howner : doubledBoxOriginIncidentOwner n m = some e) :
    doubledBoxOriginTouchesEdgeSupport n m := by
  rcases doubledBoxOriginIncidentOwner_spec_of_eq_some
      (n := n) (m := m) (e := e) howner with
    ⟨he, hme⟩
  exact
    (doubledBoxOriginTouchesEdgeSupport_iff_exists_originIncidentEdge
      (n := n) (m := m)).2 ⟨e, he, hme⟩

set_option linter.style.longLine false in

theorem doubledBoxOriginIncidentOwner_eq_some_inj
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {e f : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (he : doubledBoxOriginIncidentOwner n m = some e)
    (hf : doubledBoxOriginIncidentOwner n m = some f) :
    e = f :=
  Option.some.inj (he.symm.trans hf)

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some e) ⊆
      Ω.filter (fun m => m e ≠ 0) := by
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  exact
    ⟨hm.1,
      (doubledBoxOriginIncidentOwner_spec_of_eq_some
        (n := n) (m := m) (e := e) hm.2).2⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_filter_eq_filter_multiplicity_ne_zero
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some e) =
      Ω.filter
        (fun m => doubledBoxOriginIncidentOwner n m = some e ∧ m e ≠ 0) := by
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm ⊢
    exact
      ⟨hm.1, hm.2,
        (doubledBoxOriginIncidentOwner_spec_of_eq_some
          (n := n) (m := m) (e := e) hm.2).2⟩
  · intro hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hm.2.1⟩

set_option linter.style.longLine false in

theorem doubledBoxOriginIncidentOwner_filter_filter_multiplicity_eq_zero_eq_empty
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some e)).filter
        (fun m => m e = 0) =
      ∅ := by
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_filter] at hm
    exact False.elim
      ((doubledBoxOriginIncidentOwner_spec_of_eq_some
        (n := n) (m := m) (e := e) hm.1.2).2 hm.2)
  · simp

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupportOwner_filter_eq_filter_multiplicity_ne_zero
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Ω.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) =
      Ω.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew ∧ m ew ≠ 0) := by
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm ⊢
    exact
      ⟨hm.1, hm.2.1, hm.2.2,
        (doubledBoxOriginIncidentOwner_spec_of_eq_some
          (n := n) (m := m) (e := ew) hm.2.2).2⟩
  · intro hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hm.2.1, hm.2.2.1⟩

set_option linter.style.longLine false in

theorem doubledBoxOriginIncidentSupportOwner_filter_filter_multiplicity_eq_zero_eq_empty
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (Ω.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)).filter
        (fun m => m ew = 0) =
      ∅ := by
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_filter] at hm
    exact False.elim
      ((doubledBoxOriginIncidentOwner_spec_of_eq_some
        (n := n) (m := m) (e := ew) hm.1.2.2).2 hm.2)
  · simp

set_option linter.style.longLine false in


theorem forall_originIncidentOwnerRows_of_forall_multiplicityRows
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {P :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop}
    (hP :
      ∀ e ∈ doubledBoxOriginIncidentEdges n,
        ∀ m ∈ Ω.filter (fun m => m e ≠ 0), P e m) :
    ∀ e ∈ doubledBoxOriginIncidentEdges n,
      ∀ m ∈ Ω.filter
          (fun m => doubledBoxOriginIncidentOwner n m = some e),
        P e m := by
  intro e he m hm
  exact hP e he m <|
    doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
      (n := n) Ω e hm

set_option linter.style.longLine false in

theorem not_mem_doubledBoxOriginIncidentOwner_filter_of_ne
    {n : ℕ}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {e f : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hef : e ≠ f)
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hm : m ∈ Ω.filter
      (fun m => doubledBoxOriginIncidentOwner n m = some e)) :
    m ∉ Ω.filter
      (fun m => doubledBoxOriginIncidentOwner n m = some f) := by
  intro hmf
  rw [Finset.mem_filter] at hm hmf
  exact hef
    (doubledBoxOriginIncidentOwner_eq_some_inj
      (n := n) (m := m) hm.2 hmf.2)

set_option linter.style.longLine false in


theorem doubledBoxOriginTouchesEdgeSupport_filter_eq_biUnion_originIncidentOwnerFilters
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m) =
      (doubledBoxOriginIncidentEdges n).biUnion
        (fun e =>
          Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some e)) := by
  classical
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm
    rcases
        doubledBoxOriginIncidentOwner_exists_of_originTouchesEdgeSupport
          (n := n) (m := m) hm.2 with
      ⟨e, he, howner, _hme⟩
    rw [Finset.mem_biUnion]
    exact ⟨e, he, by rw [Finset.mem_filter]; exact ⟨hm.1, howner⟩⟩
  · intro hm
    rw [Finset.mem_biUnion] at hm
    rcases hm with ⟨e, _he, hme⟩
    rw [Finset.mem_filter] at hme ⊢
    exact
      ⟨hme.1,
        doubledBoxOriginTouchesEdgeSupport_of_originIncidentOwner_eq_some
          (n := n) (m := m) (e := e) hme.2⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginTouchesEdgeSupport_filter_card_eq_sum_originIncidentOwnerFilters_card
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m)).card =
      ∑ e ∈ doubledBoxOriginIncidentEdges n,
        (Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some e)).card := by
  classical
  rw [doubledBoxOriginTouchesEdgeSupport_filter_eq_biUnion_originIncidentOwnerFilters
    (n := n) Ω]
  rw [Finset.card_biUnion]
  intro e _he f _hf hef
  change Disjoint
    (Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some e))
    (Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some f))
  rw [Finset.disjoint_left]
  intro m hm hmf
  exact not_mem_doubledBoxOriginIncidentOwner_filter_of_ne
    (n := n) (Ω := Ω) hef hm hmf

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_eq_nonempty_originIncidentOwner_exists_mem
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hmS : doubledBoxOriginIncidentSupport n m = S)
    (hSnonempty : S.Nonempty) :
    ∃ ew ∈ S, doubledBoxOriginIncidentOwner n m = some ew ∧ m ew ≠ 0 := by
  have hsupport_nonempty : (doubledBoxOriginIncidentSupport n m).Nonempty := by
    simpa [hmS] using hSnonempty
  have htouch : doubledBoxOriginTouchesEdgeSupport n m :=
    (doubledBoxOriginIncidentSupport_nonempty_iff_originTouchesEdgeSupport
      (n := n) (m := m)).1 hsupport_nonempty
  rcases doubledBoxOriginIncidentOwner_exists_of_originTouchesEdgeSupport
      (n := n) (m := m) htouch with
    ⟨ew, hew_origin, howner, hew_pos⟩
  have hew_support : ew ∈ doubledBoxOriginIncidentSupport n m :=
    mem_doubledBoxOriginIncidentSupport.mpr ⟨hew_origin, hew_pos⟩
  have hewS : ew ∈ S := by
    simpa [hmS] using hew_support
  exact ⟨ew, hewS, howner, hew_pos⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_filter_eq_biUnion_supportPatternOwnerFilters
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hSnonempty : S.Nonempty) :
    Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S) =
      S.biUnion
        (fun ew =>
          Ω.filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew)) := by
  classical
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm
    rcases
        doubledBoxOriginIncidentSupport_eq_nonempty_originIncidentOwner_exists_mem
          (n := n) (m := m) hm.2 hSnonempty with
      ⟨ew, hewS, howner, _hew_pos⟩
    rw [Finset.mem_biUnion]
    refine ⟨ew, hewS, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hm.1, hm.2, howner⟩
  · intro hm
    rw [Finset.mem_biUnion] at hm
    rcases hm with ⟨_ew, _hewS, hm_owner⟩
    rw [Finset.mem_filter] at hm_owner ⊢
    exact ⟨hm_owner.1, hm_owner.2.1⟩

set_option linter.style.longLine false in


theorem
    doubledBoxOriginIncidentSupport_filter_card_eq_sum_supportPatternOwnerFilters_card
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hSnonempty : S.Nonempty) :
    (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S)).card =
      ∑ ew ∈ S,
        (Ω.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew)).card := by
  classical
  rw [doubledBoxOriginIncidentSupport_filter_eq_biUnion_supportPatternOwnerFilters
    (n := n) Ω hSnonempty]
  rw [Finset.card_biUnion]
  intro e _he f _hf hef
  change Disjoint
    (Ω.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some e))
    (Ω.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some f))
  rw [Finset.disjoint_left]
  intro m hm hmf
  rw [Finset.mem_filter] at hm hmf
  exact hef
    (doubledBoxOriginIncidentOwner_eq_some_inj
      (n := n) (m := m) hm.2.2 hmf.2.2)

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_filter_sum_eq_sum_supportPatternOwnerFilters
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hSnonempty : S.Nonempty)
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ) :
    (∑ m ∈ Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S),
      F m) =
      ∑ ew ∈ S,
        ∑ m ∈
          Ω.filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew),
          F m := by
  classical
  let fallback : ↥(FK.boxGraph 3 (2 * n)).edgeFinset :=
    Classical.choose hSnonempty
  let ownerClass :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset :=
    fun m => (doubledBoxOriginIncidentOwner n m).getD fallback
  calc
    (∑ m ∈ Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S),
      F m) =
        ∑ ew ∈ S,
          ∑ m ∈
            (Ω.filter
              (fun m => doubledBoxOriginIncidentSupport n m = S)).filter
              (fun m => ownerClass m = ew),
            F m := by
      exact
        finset_sum_eq_sum_fiber_filter_of_mem
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          S ownerClass F
          (by
            intro m hm
            rw [Finset.mem_filter] at hm
            rcases
                doubledBoxOriginIncidentSupport_eq_nonempty_originIncidentOwner_exists_mem
                  (n := n) (m := m) hm.2 hSnonempty with
              ⟨ew, hewS, howner, _hew_pos⟩
            simpa [ownerClass, howner] using hewS)
    _ =
        ∑ ew ∈ S,
          ∑ m ∈
            Ω.filter
              (fun m =>
                doubledBoxOriginIncidentSupport n m = S ∧
                  doubledBoxOriginIncidentOwner n m = some ew),
            F m := by
      refine Finset.sum_congr rfl ?_
      intro ew _hew
      have hfilter :
          (Ω.filter
            (fun m => doubledBoxOriginIncidentSupport n m = S)).filter
            (fun m => ownerClass m = ew) =
          Ω.filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew) := by
        ext m
        constructor
        · intro hm
          rw [Finset.mem_filter] at hm
          rw [Finset.mem_filter] at hm
          rw [Finset.mem_filter]
          rcases
              doubledBoxOriginIncidentSupport_eq_nonempty_originIncidentOwner_exists_mem
                (n := n) (m := m) hm.1.2 hSnonempty with
            ⟨owner, _hownerS, howner, _howner_pos⟩
          have howner_eq : owner = ew := by
            simpa [ownerClass, howner] using hm.2
          exact ⟨hm.1.1, hm.1.2, by simpa [howner_eq] using howner⟩
        · intro hm
          rw [Finset.mem_filter] at hm
          rw [Finset.mem_filter, Finset.mem_filter]
          exact ⟨⟨hm.1, hm.2.1⟩, by simp [ownerClass, hm.2.2]⟩
      rw [hfilter]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_filter_sum_le_sum_supportPatternOwnerBounds
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hSnonempty : S.Nonempty)
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (B : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℝ)
    (hB :
      ∀ ew ∈ S,
        (∑ m ∈
          Ω.filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew),
          F m) ≤ B ew) :
    (∑ m ∈ Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S),
      F m) ≤
      ∑ ew ∈ S, B ew := by
  rw [
    doubledBoxOriginIncidentSupport_filter_sum_eq_sum_supportPatternOwnerFilters
      (n := n) Ω hSnonempty F]
  exact Finset.sum_le_sum hB

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_filter_sum_ownerIndependentBudget_eq
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hSnonempty : S.Nonempty)
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ) :
    (∑ m ∈ Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S),
      match doubledBoxOriginIncidentOwner n m with
      | none => 0
      | some _ew => F m) =
      ∑ m ∈ Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S),
        F m := by
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [Finset.mem_filter] at hm
  by_cases howner_none : doubledBoxOriginIncidentOwner n m = none
  · have hnot_touch :
        ¬ doubledBoxOriginTouchesEdgeSupport n m :=
      (doubledBoxOriginIncidentOwner_eq_none_iff_not_originTouchesEdgeSupport
        (n := n) (m := m)).1 howner_none
    have hsupport_nonempty : (doubledBoxOriginIncidentSupport n m).Nonempty := by
      simpa [hm.2] using hSnonempty
    have htouch : doubledBoxOriginTouchesEdgeSupport n m :=
      (doubledBoxOriginIncidentSupport_nonempty_iff_originTouchesEdgeSupport
        (n := n) (m := m)).1 hsupport_nonempty
    exact False.elim (hnot_touch htouch)
  · cases howner : doubledBoxOriginIncidentOwner n m with
    | none => exact False.elim (howner_none howner)
    | some ew => rfl

set_option linter.style.longLine false in


theorem forall_originIncidentSupportPatternRows_of_forall_supportPatternOwnerRows
    {n : ℕ}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hSnonempty : S.Nonempty)
    {P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop}
    (hP :
      ∀ ew ∈ S,
        ∀ m ∈ Ω.filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew),
          P m) :
    ∀ m ∈ Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S),
      P m := by
  intro m hm
  rw [Finset.mem_filter] at hm
  rcases
      doubledBoxOriginIncidentSupport_eq_nonempty_originIncidentOwner_exists_mem
        (n := n) (m := m) hm.2 hSnonempty with
    ⟨ew, hewS, howner, _hew_pos⟩
  exact hP ew hewS m
    (by
      rw [Finset.mem_filter]
      exact ⟨hm.1, hm.2, howner⟩)

set_option linter.style.longLine false in


theorem finset_injOn_assembledRoute_of_ownerFiltered_injOn
    {α ι γ : Type*} [DecidableEq ι]
    (s : Finset α) (owners : Finset ι) (ownerOf : α → ι)
    (route : ι → α → γ)
    (howner_mem : ∀ a ∈ s, ownerOf a ∈ owners)
    (hinj :
      ∀ i ∈ owners, Set.InjOn (route i)
        (s.filter fun a => ownerOf a = i))
    (hcross :
      ∀ i ∈ owners, ∀ j ∈ owners, i ≠ j →
        ∀ a ∈ s.filter (fun a => ownerOf a = i),
          ∀ b ∈ s.filter (fun b => ownerOf b = j),
            route i a ≠ route j b) :
    Set.InjOn (fun a => route (ownerOf a) a) s := by
  intro a ha b hb hroute
  by_cases hij : ownerOf a = ownerOf b
  · have hai : a ∈ s.filter (fun x => ownerOf x = ownerOf a) := by
      exact Finset.mem_filter.mpr ⟨ha, rfl⟩
    have hbi : b ∈ s.filter (fun x => ownerOf x = ownerOf a) := by
      exact Finset.mem_filter.mpr ⟨hb, hij.symm⟩
    have hroute_same :
        route (ownerOf a) a = route (ownerOf a) b := by
      simpa [hij] using hroute
    exact hinj (ownerOf a) (howner_mem a ha) hai hbi hroute_same
  · have hai : a ∈ s.filter (fun x => ownerOf x = ownerOf a) := by
      exact Finset.mem_filter.mpr ⟨ha, rfl⟩
    have hbi : b ∈ s.filter (fun x => ownerOf x = ownerOf b) := by
      exact Finset.mem_filter.mpr ⟨hb, rfl⟩
    exact False.elim
      ((hcross (ownerOf a) (howner_mem a ha) (ownerOf b)
          (howner_mem b hb) hij a hai b hbi) hroute)

set_option linter.style.longLine false in


theorem finset_injOn_assembledRoute_of_ownerFiltered_injOn_tag
    {α ι γ : Type*} [DecidableEq ι]
    (s : Finset α) (owners : Finset ι) (ownerOf : α → ι)
    (route : ι → α → γ) (tag : γ → ι)
    (howner_mem : ∀ a ∈ s, ownerOf a ∈ owners)
    (hinj :
      ∀ i ∈ owners, Set.InjOn (route i)
        (s.filter fun a => ownerOf a = i))
    (htag :
      ∀ i ∈ owners, ∀ a ∈ s.filter (fun a => ownerOf a = i),
        tag (route i a) = i) :
    Set.InjOn (fun a => route (ownerOf a) a) s := by
  refine
    finset_injOn_assembledRoute_of_ownerFiltered_injOn
      s owners ownerOf route howner_mem hinj ?_
  intro i hi j hj hij a ha b hb hroute
  have htag_eq : tag (route i a) = tag (route j b) := congrArg tag hroute
  have hi_tag : tag (route i a) = i := htag i hi a ha
  have hj_tag : tag (route j b) = j := htag j hj b hb
  exact hij (by simpa [hi_tag, hj_tag] using htag_eq)

end Exact3D
end StatMech
