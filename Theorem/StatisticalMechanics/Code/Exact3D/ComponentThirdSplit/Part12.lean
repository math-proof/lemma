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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part11
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_cardCase
    {n : ℕ}
    (v : FK.boxVerts 3 n)
    (S : Finset (Option (FK.boxVerts 3 n))) :
    (finiteBoundaryGhostSourceClassEndpointMembershipCase v S).cardCase =
      finiteBoundaryGhostSourceClassCardinalityCase S := rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_hasGhost
    {n : ℕ}
    (v : FK.boxVerts 3 n)
    (S : Finset (Option (FK.boxVerts 3 n))) :
    (finiteBoundaryGhostSourceClassEndpointMembershipCase v S).hasGhost =
      decide (none ∈ S) := rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_hasOrigin
    {n : ℕ}
    (v : FK.boxVerts 3 n)
    (S : Finset (Option (FK.boxVerts 3 n))) :
    (finiteBoundaryGhostSourceClassEndpointMembershipCase v S).hasOrigin =
      decide (some (IsingFK.boxOrigin 3 n) ∈ S) := rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_hasEndpoint
    {n : ℕ}
    (v : FK.boxVerts 3 n)
    (S : Finset (Option (FK.boxVerts 3 n))) :
    (finiteBoundaryGhostSourceClassEndpointMembershipCase v S).hasEndpoint =
      decide (some v ∈ S) := rfl

theorem prop_iff_bool_true_of_decide_eq
    {p : Prop} [Decidable p] {b : Bool}
    (h : decide p = b) :
    p ↔ b = true := by
  by_cases hp : p <;> cases b <;> simp [hp] at h ⊢

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_cardinalityCase_of_eq
    {n : ℕ}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hcase : finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c) :
    finiteBoundaryGhostSourceClassCardinalityCase S = c.cardCase := by
  simpa [finiteBoundaryGhostSourceClassEndpointMembershipCase] using
    congrArg SourceClassEndpointMembershipCase.cardCase hcase

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_card_eq_zero_of_eq
    {n : ℕ}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hcase : finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c)
    (hc : c.cardCase = SourceClassCardinalityCase.zero) :
    S.card = 0 :=
  (finiteBoundaryGhostSourceClassCardinalityCase_eq_zero_iff_card_eq_zero
    S).mp
    ((finiteBoundaryGhostSourceClassEndpointMembershipCase_cardinalityCase_of_eq
      hcase).trans hc)

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_card_eq_two_of_eq
    {n : ℕ}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hcase : finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c)
    (hc : c.cardCase = SourceClassCardinalityCase.two) :
    S.card = 2 :=
  (finiteBoundaryGhostSourceClassCardinalityCase_eq_two_iff_card_eq_two
    S).mp
    ((finiteBoundaryGhostSourceClassEndpointMembershipCase_cardinalityCase_of_eq
      hcase).trans hc)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_card_ge_four_of_sourceClassSupport_of_eq
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hS :
      S ∈
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v)
    (hcase : finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c)
    (hc : c.cardCase = SourceClassCardinalityCase.fourPlus) :
    4 ≤ S.card :=
  finiteBoundaryGhostSourceClassCardinalityCase_fourPlus_card_ge_four_of_sourceClassSupport
    hS
    ((finiteBoundaryGhostSourceClassEndpointMembershipCase_cardinalityCase_of_eq
      hcase).trans hc)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_ghost_mem_iff_of_eq
    {n : ℕ}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hcase : finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c) :
    none ∈ S ↔ c.hasGhost = true := by
  have hbool : decide (none ∈ S) = c.hasGhost := by
    simpa [finiteBoundaryGhostSourceClassEndpointMembershipCase] using
      congrArg SourceClassEndpointMembershipCase.hasGhost hcase
  exact prop_iff_bool_true_of_decide_eq hbool

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_origin_mem_iff_of_eq
    {n : ℕ}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hcase : finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c) :
    some (IsingFK.boxOrigin 3 n) ∈ S ↔ c.hasOrigin = true := by
  have hbool :
      decide (some (IsingFK.boxOrigin 3 n) ∈ S) = c.hasOrigin := by
    simpa [finiteBoundaryGhostSourceClassEndpointMembershipCase] using
      congrArg SourceClassEndpointMembershipCase.hasOrigin hcase
  exact prop_iff_bool_true_of_decide_eq hbool

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_endpoint_mem_iff_of_eq
    {n : ℕ}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hcase : finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c) :
    some v ∈ S ↔ c.hasEndpoint = true := by
  have hbool : decide (some v ∈ S) = c.hasEndpoint := by
    simpa [finiteBoundaryGhostSourceClassEndpointMembershipCase] using
      congrArg SourceClassEndpointMembershipCase.hasEndpoint hcase
  exact prop_iff_bool_true_of_decide_eq hbool

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_ghost_notMem_of_eq_of_false
    {n : ℕ}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hcase : finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c)
    (hc : c.hasGhost = false) :
    none ∉ S := by
  intro hmem
  have htrue :
      c.hasGhost = true :=
    (finiteBoundaryGhostSourceClassEndpointMembershipCase_ghost_mem_iff_of_eq
      hcase).mp hmem
  simp [hc] at htrue

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_origin_notMem_of_eq_of_false
    {n : ℕ}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hcase : finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c)
    (hc : c.hasOrigin = false) :
    some (IsingFK.boxOrigin 3 n) ∉ S := by
  intro hmem
  have htrue :
      c.hasOrigin = true :=
    (finiteBoundaryGhostSourceClassEndpointMembershipCase_origin_mem_iff_of_eq
      hcase).mp hmem
  simp [hc] at htrue

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_endpoint_notMem_of_eq_of_false
    {n : ℕ}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hcase : finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c)
    (hc : c.hasEndpoint = false) :
    some v ∉ S := by
  intro hmem
  have htrue :
      c.hasEndpoint = true :=
    (finiteBoundaryGhostSourceClassEndpointMembershipCase_endpoint_mem_iff_of_eq
      hcase).mp hmem
  simp [hc] at htrue

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_eq_zero_of_mem
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c))
    (hc : c.cardCase = SourceClassCardinalityCase.zero) :
    S.card = 0 := by
  rcases Finset.mem_filter.mp hS with ⟨_hSsupport, hcase⟩
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipCase_card_eq_zero_of_eq
      hcase hc

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_eq_two_of_mem
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c))
    (hc : c.cardCase = SourceClassCardinalityCase.two) :
    S.card = 2 := by
  rcases Finset.mem_filter.mp hS with ⟨_hSsupport, hcase⟩
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipCase_card_eq_two_of_eq
      hcase hc

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_ge_four_of_mem
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c))
    (hc : c.cardCase = SourceClassCardinalityCase.fourPlus) :
    4 ≤ S.card := by
  rcases Finset.mem_filter.mp hS with ⟨hSsupport, hcase⟩
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipCase_card_ge_four_of_sourceClassSupport_of_eq
      hSsupport hcase hc

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_ghost_mem_iff_of_mem
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c)) :
    none ∈ S ↔ c.hasGhost = true := by
  rcases Finset.mem_filter.mp hS with ⟨_hSsupport, hcase⟩
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipCase_ghost_mem_iff_of_eq
      hcase

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_origin_mem_iff_of_mem
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c)) :
    some (IsingFK.boxOrigin 3 n) ∈ S ↔ c.hasOrigin = true := by
  rcases Finset.mem_filter.mp hS with ⟨_hSsupport, hcase⟩
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipCase_origin_mem_iff_of_eq
      hcase

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_endpoint_mem_iff_of_mem
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    {c : SourceClassEndpointMembershipCase}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c)) :
    some v ∈ S ↔ c.hasEndpoint = true := by
  rcases Finset.mem_filter.mp hS with ⟨_hSsupport, hcase⟩
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipCase_endpoint_mem_iff_of_eq
      hcase

set_option linter.style.longLine false in

theorem finset_card_two_eq_pair_of_mem
    {α : Type*} [DecidableEq α]
    {S : Finset α} {a : α}
    (hcard : S.card = 2)
    (ha : a ∈ S) :
    ∃ b, b ∈ S ∧ b ≠ a ∧ S = {a, b} := by
  classical
  have heraseCard : (S.erase a).card = 1 := by
    rw [Finset.card_erase_of_mem ha, hcard]
  rcases Finset.card_eq_one.mp heraseCard with ⟨b, hbEraseEq⟩
  have hbEraseMem : b ∈ S.erase a := by
    rw [hbEraseEq]
    simp
  have hbmem : b ∈ S := (Finset.mem_erase.mp hbEraseMem).2
  have hbne : b ≠ a := (Finset.mem_erase.mp hbEraseMem).1
  refine ⟨b, hbmem, hbne, ?_⟩
  apply Finset.Subset.antisymm
  · intro x hx
    by_cases hxa : x = a
    · simp [hxa]
    · have hxErase : x ∈ S.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
      have hxb : x = b := by
        have hxSingleton : x ∈ ({b} : Finset α) := by
          simpa [hbEraseEq] using hxErase
        simpa using hxSingleton
      simp [hxb]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · simpa [hx] using ha
    · simpa [hx] using hbmem

set_option linter.style.longLine false in

theorem finset_card_two_eq_pair_of_two_mem
    {α : Type*} [DecidableEq α]
    {S : Finset α} {a b : α}
    (hcard : S.card = 2)
    (ha : a ∈ S)
    (hb : b ∈ S)
    (hne : a ≠ b) :
    S = {a, b} := by
  classical
  have hpairSubset : ({a, b} : Finset α) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · simpa [hx] using ha
    · simpa [hx] using hb
  have hpairCard : ({a, b} : Finset α).card = 2 := Finset.card_pair hne
  have hpairEq : ({a, b} : Finset α) = S := by
    refine Finset.eq_of_subset_of_card_le hpairSubset ?_
    rw [hcard, hpairCard]
  exact hpairEq.symm

set_option linter.style.longLine false in


theorem finset_sum_filter_eq_eq_singleton_or_zero
    {α : Type*} [DecidableEq α]
    (support : Finset α)
    (f : α → ℝ)
    (a : α) :
    (∑ x ∈ support.filter (fun x => x = a), f x) =
      if a ∈ support then f a else 0 := by
  classical
  have hfilter :
      support.filter (fun x => x = a) =
        if a ∈ support then {a} else ∅ := by
    by_cases ha : a ∈ support
    · rw [if_pos ha]
      ext x
      constructor
      · intro hx
        simpa using (Finset.mem_filter.mp hx).2
      · intro hx
        have hxa : x = a := by simpa using hx
        subst x
        exact Finset.mem_filter.mpr ⟨ha, rfl⟩
    · rw [if_neg ha]
      ext x
      constructor
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨hxsupport, hxa⟩
        subst x
        exact False.elim (ha hxsupport)
      · intro hx
        simp at hx
  rw [hfilter]
  by_cases ha : a ∈ support
  · simp [ha]
  · simp [ha]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_eq_zeroEmpty_of_cardCase_zero
    {n : ℕ}
    (v : FK.boxVerts 3 n)
    (S : Finset (Option (FK.boxVerts 3 n)))
    (hzero :
      (finiteBoundaryGhostSourceClassEndpointMembershipCase v S).cardCase =
        SourceClassCardinalityCase.zero) :
    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
      finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase := by
  classical
  have hcardCase :
      finiteBoundaryGhostSourceClassCardinalityCase S =
        SourceClassCardinalityCase.zero := by
    simpa [finiteBoundaryGhostSourceClassEndpointMembershipCase] using hzero
  have hcard : S.card = 0 :=
    (finiteBoundaryGhostSourceClassCardinalityCase_eq_zero_iff_card_eq_zero
      S).mp hcardCase
  have hEmpty : S = ∅ := Finset.card_eq_zero.mp hcard
  simp [finiteBoundaryGhostSourceClassEndpointMembershipCase,
    finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase,
    finiteBoundaryGhostSourceClassCardinalityCase, hEmpty]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipCase_eq_zeroEmpty_iff
    {n : ℕ}
    (v : FK.boxVerts 3 n)
    (S : Finset (Option (FK.boxVerts 3 n))) :
    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
        finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase ↔
      S = ∅ := by
  constructor
  · intro hcase
    have hcard : S.card = 0 :=
      finiteBoundaryGhostSourceClassEndpointMembershipCase_card_eq_zero_of_eq
        hcase rfl
    exact Finset.card_eq_zero.mp hcard
  · intro hEmpty
    subst S
    simp [finiteBoundaryGhostSourceClassEndpointMembershipCase,
      finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase,
      finiteBoundaryGhostSourceClassCardinalityCase]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_zeroEmpty_eq_filter_empty
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase) =
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter (fun S => S = ∅) := by
  ext S
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipCase_eq_zeroEmpty_iff]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_zero_ne_emptyCase_eq_empty
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (c : SourceClassEndpointMembershipCase)
    (hczero : c.cardCase = SourceClassCardinalityCase.zero)
    (hcne :
      c ≠ finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c) =
      ∅ := by
  classical
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨_hSsupport, hcase⟩
    have hzero :
        (finiteBoundaryGhostSourceClassEndpointMembershipCase v S).cardCase =
          SourceClassCardinalityCase.zero := by
      simpa [hcase] using hczero
    have hlabel :
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase :=
      finiteBoundaryGhostSourceClassEndpointMembershipCase_eq_zeroEmpty_of_cardCase_zero
        v S hzero
    have hcempty :
        c = finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase :=
      hcase.symm.trans hlabel
    exact False.elim (hcne hcempty)
  · intro hS
    simp at hS

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport_source_ne_twoPoint
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v}
    (hD :
      D ∈ finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
        n Ω v) :
    D.1 ≠
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  unfold finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport at hD
  exact (Finset.mem_filter.mp hD).2

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_ne_twoPoint
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v) :
    S ≠
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  rcases Finset.mem_image.mp hS with ⟨D, hD, hDS⟩
  rw [← hDS]
  exact
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport_source_ne_twoPoint
      hD

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_origin_endpoint_noGhost_eq_empty
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointNoGhostCase) =
      ∅ := by
  classical
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSsupport, hcase⟩
    have hcardCase :
        finiteBoundaryGhostSourceClassCardinalityCase S =
          SourceClassCardinalityCase.two := by
      simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipCase,
        finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointNoGhostCase]
        using congrArg SourceClassEndpointMembershipCase.cardCase hcase
    have horiginBool :
        decide (some (IsingFK.boxOrigin 3 n) ∈ S) = true := by
      simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipCase,
        finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointNoGhostCase]
        using congrArg SourceClassEndpointMembershipCase.hasOrigin hcase
    have hendpointBool : decide (some v ∈ S) = true := by
      simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipCase,
        finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointNoGhostCase]
        using congrArg SourceClassEndpointMembershipCase.hasEndpoint hcase
    have hcard : S.card = 2 := by
      unfold finiteBoundaryGhostSourceClassCardinalityCase at hcardCase
      by_cases hzero : S.card = 0
      · simp [hzero] at hcardCase
      · by_cases htwo : S.card = 2
        · exact htwo
        · simp [hzero, htwo] at hcardCase
    have horigin : some (IsingFK.boxOrigin 3 n) ∈ S :=
      of_decide_eq_true horiginBool
    have hendpoint : some v ∈ S :=
      of_decide_eq_true hendpointBool
    have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
    have horigin_ne_v : IsingFK.boxOrigin 3 n ≠ v :=
      boxOrigin_ne_of_boxBoundary 3 n hvbdry
    have hsome_ne :
        some (IsingFK.boxOrigin 3 n) ≠
          (some v : Option (FK.boxVerts 3 n)) := by
      intro hsome
      exact horigin_ne_v (Option.some.inj hsome)
    have hpairSubset :
        ({some (IsingFK.boxOrigin 3 n), some v} :
          Finset (Option (FK.boxVerts 3 n))) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · simpa [hx] using horigin
      · simpa [hx] using hendpoint
    have hpairCard :
        ({some (IsingFK.boxOrigin 3 n), some v} :
          Finset (Option (FK.boxVerts 3 n))).card = 2 :=
      Finset.card_pair hsome_ne
    have hpairEq :
        ({some (IsingFK.boxOrigin 3 n), some v} :
          Finset (Option (FK.boxVerts 3 n))) = S := by
      refine Finset.eq_of_subset_of_card_le hpairSubset ?_
      rw [hcard, hpairCard]
    have hsymm :
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) =
          ({some (IsingFK.boxOrigin 3 n), some v} :
            Finset (Option (FK.boxVerts 3 n))) := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton,
        Finset.mem_insert]
      constructor
      · rintro (⟨hmem, _hnot⟩ | ⟨hmem, _hnot⟩)
        · left
          exact hmem
        · right
          exact hmem
      · rintro (hmem | hmem)
        · left
          exact ⟨hmem, fun hvx => hsome_ne (hmem.symm.trans hvx)⟩
        · right
          exact ⟨hmem, fun hox => hsome_ne (hox.symm.trans hmem)⟩
    have hS_twoPoint :
        S =
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) :=
      hpairEq.symm.trans hsymm.symm
    exact False.elim
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_ne_twoPoint
        hSsupport hS_twoPoint)
  · intro hS
    simp at hS

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport_filter_twoPoint_eq_empty
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
        n Ω v).filter
      (fun D =>
        D.1 =
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) =
      ∅ := by
  classical
  ext D
  constructor
  · intro hD
    rcases Finset.mem_filter.mp hD with ⟨hDsupport, hDclass⟩
    exact False.elim
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport_source_ne_twoPoint
        hDsupport hDclass)
  · intro hD
    simp at hD

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport_filter_twoPoint_card_eq_zero
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    ((finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
        n Ω v).filter
      (fun D =>
        D.1 =
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))).card =
      0 := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport_filter_twoPoint_eq_empty]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_twoPoint_eq_zero
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) =
      0 := by
  classical
  unfold finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
  refine Finset.sum_eq_zero ?_
  intro D hD
  rcases Finset.mem_filter.mp hD with ⟨hDsupport, hDclass⟩
  exact False.elim
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport_source_ne_twoPoint
      hDsupport hDclass)

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_origin_endpoint_noGhost_sum_eq_zero
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
            finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointNoGhostCase),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) = 0 := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_origin_endpoint_noGhost_eq_empty
      n Ω v hv]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_ne_emptyCase_sum_eq_zero
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (c : SourceClassEndpointMembershipCase)
    (hczero : c.cardCase = SourceClassCardinalityCase.zero)
    (hcne :
      c ≠ finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) = 0 := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_zero_ne_emptyCase_eq_empty
      n Ω v c hczero hcne]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_origin_endpoint_ghost_eq_empty
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointGhostCase) =
      ∅ := by
  classical
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨_hSsupport, hcase⟩
    have hcardCase :
        finiteBoundaryGhostSourceClassCardinalityCase S =
          SourceClassCardinalityCase.two := by
      simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipCase,
        finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointGhostCase]
        using congrArg SourceClassEndpointMembershipCase.cardCase hcase
    have hghostBool : decide (none ∈ S) = true := by
      simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipCase,
        finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointGhostCase]
        using congrArg SourceClassEndpointMembershipCase.hasGhost hcase
    have horiginBool :
        decide (some (IsingFK.boxOrigin 3 n) ∈ S) = true := by
      simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipCase,
        finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointGhostCase]
        using congrArg SourceClassEndpointMembershipCase.hasOrigin hcase
    have hendpointBool : decide (some v ∈ S) = true := by
      simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipCase,
        finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointGhostCase]
        using congrArg SourceClassEndpointMembershipCase.hasEndpoint hcase
    have hcard : S.card = 2 :=
      (finiteBoundaryGhostSourceClassCardinalityCase_eq_two_iff_card_eq_two
        S).mp hcardCase
    have hghost : none ∈ S :=
      of_decide_eq_true hghostBool
    have horigin : some (IsingFK.boxOrigin 3 n) ∈ S :=
      of_decide_eq_true horiginBool
    have hendpoint : some v ∈ S :=
      of_decide_eq_true hendpointBool
    have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
    have horigin_ne_v : IsingFK.boxOrigin 3 n ≠ v :=
      boxOrigin_ne_of_boxBoundary 3 n hvbdry
    have horigin_ne_endpoint :
        some (IsingFK.boxOrigin 3 n) ≠
          (some v : Option (FK.boxVerts 3 n)) := by
      intro hsome
      exact horigin_ne_v (Option.some.inj hsome)
    have htripleSubset :
        ({none, some (IsingFK.boxOrigin 3 n), some v} :
          Finset (Option (FK.boxVerts 3 n))) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · simpa [hx] using hghost
      · simpa [hx] using horigin
      · simpa [hx] using hendpoint
    have hnone_not_pair :
        (none : Option (FK.boxVerts 3 n)) ∉
          ({some (IsingFK.boxOrigin 3 n), some v} :
            Finset (Option (FK.boxVerts 3 n))) := by
      simp
    have htripleCard :
        ({none, some (IsingFK.boxOrigin 3 n), some v} :
          Finset (Option (FK.boxVerts 3 n))).card = 3 := by
      rw [Finset.card_insert_of_notMem hnone_not_pair]
      rw [Finset.card_pair horigin_ne_endpoint]
    have hthree_le : 3 ≤ S.card := by
      simpa [htripleCard] using Finset.card_le_card htripleSubset
    omega
  · intro hS
    simp at hS

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_origin_endpoint_ghost_sum_eq_zero
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
            finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointGhostCase),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) = 0 := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_origin_endpoint_ghost_eq_empty
      n Ω v hv]
  simp

end Exact3D
end StatMech
