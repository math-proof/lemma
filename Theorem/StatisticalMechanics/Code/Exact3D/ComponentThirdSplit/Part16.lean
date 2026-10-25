/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part16
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_iff
    {n : ℕ} {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {x : Option (FK.boxVerts 3 n)} :
    x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S ↔
      x ∈ S ∧ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v := by
  classical
  simp [finiteBoundaryGhostSourceClassEndpointUnmarkedResidual]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_powerset
    {n : ℕ} (v : FK.boxVerts 3 n)
    (S : Finset (Option (FK.boxVerts 3 n))) :
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S ∈
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset := by
  classical
  exact Finset.mem_powerset.mpr
    (by
      intro x hx
      exact
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_iff.mp
          hx).2)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
    {n : ℕ}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {cardCase : SourceClassCardinalityCase}
    {hasGhost hasOrigin hasEndpoint : Bool}
    (hcase :
      finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
        finiteBoundaryGhostSourceClassEndpointMembershipLabel
          cardCase hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMarkedSources
        v hasGhost hasOrigin hasEndpoint ∪
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S =
        S := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hmarked | hresidual
    · rcases
        (finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mp
          hmarked) with
        ⟨hxnone, hghost⟩ | ⟨hxorigin, horigin⟩ | ⟨hxendpoint, hendpoint⟩
      · subst x
        exact
          (finiteBoundaryGhostSourceClassEndpointMembershipCase_ghost_mem_iff_of_eq
            hcase).mpr
            (by
              simpa [finiteBoundaryGhostSourceClassEndpointMembershipLabel]
                using hghost)
      · subst x
        exact
          (finiteBoundaryGhostSourceClassEndpointMembershipCase_origin_mem_iff_of_eq
            hcase).mpr
            (by
              simpa [finiteBoundaryGhostSourceClassEndpointMembershipLabel]
                using horigin)
      · subst x
        exact
          (finiteBoundaryGhostSourceClassEndpointMembershipCase_endpoint_mem_iff_of_eq
            hcase).mpr
            (by
              simpa [finiteBoundaryGhostSourceClassEndpointMembershipLabel]
                using hendpoint)
    · exact
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_iff.mp
          hresidual).1
  · intro hxS
    by_cases hxnone : x = none
    · subst x
      have hghost :
          hasGhost = true := by
        simpa [finiteBoundaryGhostSourceClassEndpointMembershipLabel] using
          (finiteBoundaryGhostSourceClassEndpointMembershipCase_ghost_mem_iff_of_eq
            hcase).mp hxS
      exact Finset.mem_union.mpr
        (Or.inl
          (finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mpr
            (Or.inl ⟨rfl, hghost⟩)))
    · by_cases hxorigin : x = some (IsingFK.boxOrigin 3 n)
      · subst x
        have horigin :
            hasOrigin = true := by
          simpa [finiteBoundaryGhostSourceClassEndpointMembershipLabel] using
            (finiteBoundaryGhostSourceClassEndpointMembershipCase_origin_mem_iff_of_eq
              hcase).mp hxS
        exact Finset.mem_union.mpr
          (Or.inl
            (finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mpr
              (Or.inr (Or.inl ⟨rfl, horigin⟩))))
      · by_cases hxendpoint : x = some v
        · subst x
          have hendpoint :
              hasEndpoint = true := by
            simpa [finiteBoundaryGhostSourceClassEndpointMembershipLabel] using
              (finiteBoundaryGhostSourceClassEndpointMembershipCase_endpoint_mem_iff_of_eq
                hcase).mp hxS
          exact Finset.mem_union.mpr
            (Or.inl
              (finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mpr
                (Or.inr (Or.inr ⟨rfl, hendpoint⟩))))
        · exact Finset.mem_union.mpr
            (Or.inr
              (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_iff.mpr
                ⟨hxS,
                  finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff.mpr
                    ⟨hxnone, hxorigin, hxendpoint⟩⟩))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_subset_markedResidualImage
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (cardCase : SourceClassCardinalityCase)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            cardCase hasGhost hasOrigin hasEndpoint) ⊆
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.image
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R) := by
  classical
  intro S hS
  rcases Finset.mem_filter.mp hS with ⟨_hSsupport, hcase⟩
  exact Finset.mem_image.mpr
    ⟨finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S,
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_powerset v S,
      finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
        hcase⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_fourPlus_subset_markedResidualCardImage
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.fourPlus
            hasGhost hasOrigin hasEndpoint) ⊆
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          4 ≤
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v hasGhost hasOrigin hasEndpoint ∪ R).card)).image
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R) := by
  classical
  intro S hS
  rcases Finset.mem_filter.mp hS with ⟨_hSsupport, hcase⟩
  let R := finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S
  have hRpow :
      R ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset := by
    simpa [R] using
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_powerset v S
  have hunion :
      finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R =
        S := by
    simpa [R] using
      finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
        hcase
  have hcard :
      4 ≤ S.card :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_ge_four_of_mem
      hS rfl
  exact Finset.mem_image.mpr
    ⟨R,
      Finset.mem_filter.mpr
        ⟨hRpow, by simpa [hunion] using hcard⟩,
      hunion⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_endpoint_exists_unmarked_pair
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.two false false true)) :
    ∃ x,
      x ∈ S ∧
      x ≠ some v ∧
      x ≠ none ∧
      x ≠ some (IsingFK.boxOrigin 3 n) ∧
      S = {some v, x} := by
  classical
  have hcard : S.card = 2 :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_eq_two_of_mem
      hS rfl
  have hendpoint : some v ∈ S :=
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_endpoint_mem_iff_of_mem
      hS).mpr rfl
  have hghostAbs : none ∉ S := by
    intro hmem
    have htrue :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_ghost_mem_iff_of_mem
        hS).mp hmem
    simp [finiteBoundaryGhostSourceClassEndpointMembershipLabel] at htrue
  have horiginAbs : some (IsingFK.boxOrigin 3 n) ∉ S := by
    intro hmem
    have htrue :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_origin_mem_iff_of_mem
        hS).mp hmem
    simp [finiteBoundaryGhostSourceClassEndpointMembershipLabel] at htrue
  rcases finset_card_two_eq_pair_of_mem hcard hendpoint with
    ⟨x, hxmem, hxneEndpoint, hpair⟩
  refine ⟨x, hxmem, hxneEndpoint, ?_, ?_, hpair⟩
  · intro hx
    exact hghostAbs (by simpa [hx] using hxmem)
  · intro hx
    exact horiginAbs (by simpa [hx] using hxmem)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_origin_exists_unmarked_pair
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.two false true false)) :
    ∃ x,
      x ∈ S ∧
      x ≠ some (IsingFK.boxOrigin 3 n) ∧
      x ≠ none ∧
      x ≠ some v ∧
      S = {some (IsingFK.boxOrigin 3 n), x} := by
  classical
  have hcard : S.card = 2 :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_eq_two_of_mem
      hS rfl
  have horigin : some (IsingFK.boxOrigin 3 n) ∈ S :=
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_origin_mem_iff_of_mem
      hS).mpr rfl
  have hghostAbs : none ∉ S := by
    intro hmem
    have htrue :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_ghost_mem_iff_of_mem
        hS).mp hmem
    simp [finiteBoundaryGhostSourceClassEndpointMembershipLabel] at htrue
  have hendpointAbs : some v ∉ S := by
    intro hmem
    have htrue :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_endpoint_mem_iff_of_mem
        hS).mp hmem
    simp [finiteBoundaryGhostSourceClassEndpointMembershipLabel] at htrue
  rcases finset_card_two_eq_pair_of_mem hcard horigin with
    ⟨x, hxmem, hxneOrigin, hpair⟩
  refine ⟨x, hxmem, hxneOrigin, ?_, ?_, hpair⟩
  · intro hx
    exact hghostAbs (by simpa [hx] using hxmem)
  · intro hx
    exact hendpointAbs (by simpa [hx] using hxmem)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_ghost_exists_unmarked_pair
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.two true false false)) :
    ∃ x,
      x ∈ S ∧
      x ≠ none ∧
      x ≠ some (IsingFK.boxOrigin 3 n) ∧
      x ≠ some v ∧
      S = {none, x} := by
  classical
  have hcard : S.card = 2 :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_eq_two_of_mem
      hS rfl
  have hghost : none ∈ S :=
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_ghost_mem_iff_of_mem
      hS).mpr rfl
  have horiginAbs : some (IsingFK.boxOrigin 3 n) ∉ S := by
    intro hmem
    have htrue :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_origin_mem_iff_of_mem
        hS).mp hmem
    simp [finiteBoundaryGhostSourceClassEndpointMembershipLabel] at htrue
  have hendpointAbs : some v ∉ S := by
    intro hmem
    have htrue :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_endpoint_mem_iff_of_mem
        hS).mp hmem
    simp [finiteBoundaryGhostSourceClassEndpointMembershipLabel] at htrue
  rcases finset_card_two_eq_pair_of_mem hcard hghost with
    ⟨x, hxmem, hxneGhost, hpair⟩
  refine ⟨x, hxmem, hxneGhost, ?_, ?_, hpair⟩
  · intro hx
    exact horiginAbs (by simpa [hx] using hxmem)
  · intro hx
    exact hendpointAbs (by simpa [hx] using hxmem)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_ghost_endpoint_eq_pair
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.two true false true)) :
    S = ({none, some v} : Finset (Option (FK.boxVerts 3 n))) := by
  classical
  have hcard : S.card = 2 :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_eq_two_of_mem
      hS rfl
  have hghost : none ∈ S :=
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_ghost_mem_iff_of_mem
      hS).mpr rfl
  have hendpoint : some v ∈ S :=
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_endpoint_mem_iff_of_mem
      hS).mpr rfl
  exact finset_card_two_eq_pair_of_two_mem hcard hghost hendpoint (by simp)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_ghost_origin_eq_pair
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.two true true false)) :
    S =
      ({none, some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) := by
  classical
  have hcard : S.card = 2 :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_eq_two_of_mem
      hS rfl
  have hghost : none ∈ S :=
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_ghost_mem_iff_of_mem
      hS).mpr rfl
  have horigin : some (IsingFK.boxOrigin 3 n) ∈ S :=
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_origin_mem_iff_of_mem
      hS).mpr rfl
  exact finset_card_two_eq_pair_of_two_mem hcard hghost horigin (by simp)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_ghost_endpoint_eq_filter_pair
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.two true false true) =
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          S = ({none, some v} : Finset (Option (FK.boxVerts 3 n)))) := by
  classical
  ext S
  constructor
  · intro hS
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hS).1,
        finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_ghost_endpoint_eq_pair
          hS⟩
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSsupport, hpair⟩
    refine Finset.mem_filter.mpr ⟨hSsupport, ?_⟩
    subst S
    have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
    have horigin_ne_v : IsingFK.boxOrigin 3 n ≠ v :=
      boxOrigin_ne_of_boxBoundary 3 n hvbdry
    simp [finiteBoundaryGhostSourceClassEndpointMembershipCase,
      finiteBoundaryGhostSourceClassEndpointMembershipLabel,
      finiteBoundaryGhostSourceClassCardinalityCase, horigin_ne_v]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_ghost_origin_eq_filter_pair
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.two true true false) =
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          S =
            ({none, some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n)))) := by
  classical
  ext S
  constructor
  · intro hS
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hS).1,
        finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_ghost_origin_eq_pair
          hS⟩
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSsupport, hpair⟩
    refine Finset.mem_filter.mpr ⟨hSsupport, ?_⟩
    subst S
    have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
    have hv_ne_origin : v ≠ IsingFK.boxOrigin 3 n := by
      intro h
      exact boxOrigin_ne_of_boxBoundary 3 n hvbdry h.symm
    simp [finiteBoundaryGhostSourceClassEndpointMembershipCase,
      finiteBoundaryGhostSourceClassEndpointMembershipLabel,
      finiteBoundaryGhostSourceClassCardinalityCase, hv_ne_origin]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_endpoint_sum_eq_pairSourceClassSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.two true false true),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      if ({none, some v} : Finset (Option (FK.boxVerts 3 n))) ∈
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v then
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v ({none, some v} : Finset (Option (FK.boxVerts 3 n)))
      else
        0 := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_ghost_endpoint_eq_filter_pair
      n Ω v hv]
  exact
    finset_sum_filter_eq_eq_singleton_or_zero
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v)
      (fun S =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S)
      ({none, some v} : Finset (Option (FK.boxVerts 3 n)))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_origin_sum_eq_pairSourceClassSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.two true true false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      if ({none, some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∈
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v then
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          ({none, some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n)))
      else
        0 := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_ghost_origin_eq_filter_pair
      n Ω v hv]
  exact
    finset_sum_filter_eq_eq_singleton_or_zero
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v)
      (fun S =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S)
      ({none, some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n)))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_none_exists_unmarked_pair
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.two false false false)) :
    ∃ x y,
      x ∈ S ∧
      y ∈ S ∧
      x ≠ y ∧
      x ≠ none ∧
      y ≠ none ∧
      x ≠ some (IsingFK.boxOrigin 3 n) ∧
      y ≠ some (IsingFK.boxOrigin 3 n) ∧
      x ≠ some v ∧
      y ≠ some v ∧
      S = {x, y} := by
  classical
  have hcard : S.card = 2 :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_eq_two_of_mem
      hS rfl
  have hghostAbs : none ∉ S := by
    intro hmem
    have htrue :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_ghost_mem_iff_of_mem
        hS).mp hmem
    simp [finiteBoundaryGhostSourceClassEndpointMembershipLabel] at htrue
  have horiginAbs : some (IsingFK.boxOrigin 3 n) ∉ S := by
    intro hmem
    have htrue :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_origin_mem_iff_of_mem
        hS).mp hmem
    simp [finiteBoundaryGhostSourceClassEndpointMembershipLabel] at htrue
  have hendpointAbs : some v ∉ S := by
    intro hmem
    have htrue :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_endpoint_mem_iff_of_mem
        hS).mp hmem
    simp [finiteBoundaryGhostSourceClassEndpointMembershipLabel] at htrue
  have honeLt : 1 < S.card := by omega
  rcases (Finset.one_lt_card.mp honeLt) with ⟨x, hxmem, y, hymem, hxy⟩
  have hpair : S = {x, y} :=
    finset_card_two_eq_pair_of_two_mem hcard hxmem hymem hxy
  refine
    ⟨x, y, hxmem, hymem, hxy, ?_, ?_, ?_, ?_, ?_, ?_, hpair⟩
  · intro hx
    exact hghostAbs (by simpa [hx] using hxmem)
  · intro hy
    exact hghostAbs (by simpa [hy] using hymem)
  · intro hx
    exact horiginAbs (by simpa [hx] using hxmem)
  · intro hy
    exact horiginAbs (by simpa [hy] using hymem)
  · intro hx
    exact hendpointAbs (by simpa [hx] using hxmem)
  · intro hy
    exact hendpointAbs (by simpa [hy] using hymem)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_endpoint_subset_unmarkedPairImage
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.two false false true) ⊆
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).image
        (fun x => ({some v, x} : Finset (Option (FK.boxVerts 3 n)))) := by
  classical
  intro S hS
  rcases
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_endpoint_exists_unmarked_pair
      hS with
    ⟨x, _hxmem, hxneEndpoint, hxneGhost, hxneOrigin, hpair⟩
  exact Finset.mem_image.mpr
    ⟨x,
      finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff.mpr
        ⟨hxneGhost, hxneOrigin, hxneEndpoint⟩,
      hpair.symm⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_origin_subset_unmarkedPairImage
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.two false true false) ⊆
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).image
        (fun x =>
          ({some (IsingFK.boxOrigin 3 n), x} :
            Finset (Option (FK.boxVerts 3 n)))) := by
  classical
  intro S hS
  rcases
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_origin_exists_unmarked_pair
      hS with
    ⟨x, _hxmem, hxneOrigin, hxneGhost, hxneEndpoint, hpair⟩
  exact Finset.mem_image.mpr
    ⟨x,
      finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff.mpr
        ⟨hxneGhost, hxneOrigin, hxneEndpoint⟩,
      hpair.symm⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_ghost_subset_unmarkedPairImage
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.two true false false) ⊆
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).image
        (fun x => ({none, x} : Finset (Option (FK.boxVerts 3 n)))) := by
  classical
  intro S hS
  rcases
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_ghost_exists_unmarked_pair
      hS with
    ⟨x, _hxmem, hxneGhost, hxneOrigin, hxneEndpoint, hpair⟩
  exact Finset.mem_image.mpr
    ⟨x,
      finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff.mpr
        ⟨hxneGhost, hxneOrigin, hxneEndpoint⟩,
      hpair.symm⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_none_subset_unmarkedPairImage
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.two false false false) ⊆
      Finset.image₂
        (fun x y => ({x, y} : Finset (Option (FK.boxVerts 3 n))))
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v)
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v) := by
  classical
  intro S hS
  rcases
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_two_none_exists_unmarked_pair
      hS with
    ⟨x, y, _hxmem, _hymem, _hxy, hxneGhost, hyneGhost,
      hxneOrigin, hyneOrigin, hxneEndpoint, hyneEndpoint, hpair⟩
  exact Finset.mem_image₂.mpr
    ⟨x,
      finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff.mpr
        ⟨hxneGhost, hxneOrigin, hxneEndpoint⟩,
      y,
      finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff.mpr
        ⟨hyneGhost, hyneOrigin, hyneEndpoint⟩,
      hpair.symm⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_zero_none_eq_filter_empty
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.zero false false false) =
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter (fun S => S = ∅) := by
  simpa [
    finiteBoundaryGhostSourceClassEndpointMembershipLabel_zero_none_eq_zeroEmpty]
    using
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_zeroEmpty_eq_filter_empty
        n Ω v

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_none_sum_eq_emptySourceClassSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.zero false false false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      if (∅ : Finset (Option (FK.boxVerts 3 n))) ∈
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v then
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v ∅
      else
        0 := by
  classical
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ω v
  have hfilter :
      sourceClassSupport.filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.zero false false false) =
        if (∅ : Finset (Option (FK.boxVerts 3 n))) ∈ sourceClassSupport then
          {∅}
        else
          ∅ := by
    rw [
      show
        sourceClassSupport.filter
            (fun S =>
              finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                finiteBoundaryGhostSourceClassEndpointMembershipLabel
                  SourceClassCardinalityCase.zero false false false) =
          sourceClassSupport.filter (fun S => S = ∅) by
        simpa [sourceClassSupport] using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_zero_none_eq_filter_empty
            n Ω v]
    by_cases hmem :
        (∅ : Finset (Option (FK.boxVerts 3 n))) ∈ sourceClassSupport
    · rw [if_pos hmem]
      ext S
      constructor
      · intro hS
        simpa using (Finset.mem_filter.mp hS).2
      · intro hS
        have hSempty : S = ∅ := by
          simpa using hS
        subst S
        exact Finset.mem_filter.mpr ⟨hmem, rfl⟩
    · rw [if_neg hmem]
      ext S
      constructor
      · intro hS
        rcases Finset.mem_filter.mp hS with ⟨hSsupport, hSempty⟩
        subst S
        exact False.elim (hmem hSsupport)
      · intro hS
        simp at hS
  rw [show
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.zero false false false) =
        sourceClassSupport.filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.zero false false false) by
      rfl]
  rw [hfilter]
  by_cases hmem :
      (∅ : Finset (Option (FK.boxVerts 3 n))) ∈ sourceClassSupport
  · simp [sourceClassSupport, hmem]
  · simp [sourceClassSupport, hmem]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_none_sum_eq_zero_of_empty_notMem
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hnot :
      (∅ : Finset (Option (FK.boxVerts 3 n))) ∉
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.zero false false false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) = 0 := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_none_sum_eq_emptySourceClassSum]
  simp [hnot]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_none_sum_eq_emptySourceClassSum_of_empty_mem
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hmem :
      (∅ : Finset (Option (FK.boxVerts 3 n))) ∈
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.zero false false false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v ∅ := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_none_sum_eq_emptySourceClassSum]
  simp [hmem]

end Exact3D
end StatMech
