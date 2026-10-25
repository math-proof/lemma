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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part9
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_eq_zero_of_not_mem_sourceClassSupport
    (β H : ℝ) {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∉
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S = 0 := by
  classical
  unfold finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
  refine Finset.sum_eq_zero ?_
  intro D hD
  rcases Finset.mem_filter.mp hD with ⟨hDsupport, hDsource⟩
  exact False.elim
    (hS (Finset.mem_image.mpr ⟨D, hDsupport, hDsource⟩))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData_fullSource
    {n : ℕ} {v : FK.boxVerts 3 n}
    (D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) D.2.1)
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) D.2.1)) = D.1 := by
  simpa using
    finiteBoundaryGhostFullSourceClassifiedTwoPointSourceData_fullSource D.2

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData_fullSource_card_even
    {n : ℕ} {v : FK.boxVerts 3 n}
    (D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v) :
    Even D.1.card := by
  have hhandshake :
      Even
        (Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) D.2.1)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) D.2.1))).card :=
    StatMech.Walls.gc7_total_handshake_edgeCopy
      (Sharpness.withGhost (FK.boxGraph 3 n)) D.2.1
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) D.2.1))
  have hsource :=
    finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData_fullSource D
  simpa [hsource] using hhandshake

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport_source_card_even
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v}
    (_hD :
      D ∈ finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
        n Ω v) :
    Even D.1.card :=
  finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData_fullSource_card_even D

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_card_even
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v) :
    Even S.card := by
  classical
  rcases Finset.mem_image.mp hS with ⟨D, hD, hDS⟩
  rw [← hDS]
  exact
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport_source_card_even
      hD

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_card_odd_eq_empty
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter (fun S => Odd S.card) =
      ∅ := by
  classical
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSsupport, hSodd⟩
    have hSeven :
        Even S.card :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_card_even
        hSsupport
    rcases hSeven with ⟨a, ha⟩
    rcases hSodd with ⟨b, hb⟩
    omega
  · intro hS
    simp at hS

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_cardOdd_sum_eq_zero
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter (fun S => Odd S.card),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) = 0 := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_card_odd_eq_empty]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_card_eq_zero_or_two_or_four_le
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v) :
    S.card = 0 ∨ S.card = 2 ∨ 4 ≤ S.card := by
  have hSeven :
      Even S.card :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_card_even
      hS
  rcases hSeven with ⟨k, hk⟩
  by_cases hklt : k < 2
  · have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · left
      omega
    · right
      left
      omega
  · right
    right
    omega


end Exact3D
end StatMech
