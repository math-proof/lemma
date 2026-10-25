/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_toprowrun.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc_runnoup
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Structure.StatisticalMechanics.Code.Walls.jc2_runframe
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc2_RunFrame.isExtreme {K : Set (Site 2)} {c : Site 2} {len : ℤ}
    (h : jc2_RunFrame K c len) : IsExtremeCell K c :=
  h.isRun.isExtreme


theorem jc2_RunFrame.len_nonneg {K : Set (Site 2)} {c : Site 2} {len : ℤ}
    (h : jc2_RunFrame K c len) : 0 ≤ len :=
  h.isRun.len_nonneg


theorem jc2_RunFrame.run_mem {K : Set (Site 2)} {c : Site 2} {len : ℤ}
    (h : jc2_RunFrame K c len) (j : ℤ) (hj0 : 0 ≤ j) (hj1 : j ≤ len) : (c + ![j, 0]) ∈ K :=
  h.isRun.run_mem j hj0 hj1


theorem jc2_RunFrame.mem {K : Set (Site 2)} {c : Site 2} {len : ℤ}
    (h : jc2_RunFrame K c len) : c ∈ K :=
  h.isRun.isExtreme.mem


theorem jc2_runFrame_of_extremeCell (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) : jc2_RunFrame K c (jc_runMax K c : ℤ) := by
  have hrun : jc_IsTopRowRun K c (jc_runMax K c : ℤ) := jc2_isTopRowRun_of_extremeCell K hK c hc
  obtain ⟨hnoup, hleft, hright⟩ := jc_runFrame K c (jc_runMax K c : ℤ) hrun
  exact ⟨hrun, hnoup, hleft, hright⟩


theorem jc2_runFrame_of_earAnchor (K : Set (Site 2)) (hK : K.Finite) {c : Site 2}
    (hanchor : jc_EarAnchor K c) : jc2_RunFrame K c (jc_runMax K c : ℤ) :=
  jc2_runFrame_of_extremeCell K hK c hanchor.isExtreme


theorem jc2_runFrame (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c len, jc2_RunFrame K c len := by
  obtain ⟨c, hanchor⟩ := jc_earAnchor K hK hne
  exact ⟨c, jc_runMax K c, jc2_runFrame_of_earAnchor K hK hanchor⟩


theorem jc2_runFrame_explicit (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c len, c ∈ K ∧ 0 ≤ len ∧ (∀ j : ℤ, 0 ≤ j → j ≤ len → (c + ![j, 0]) ∈ K) ∧
      (c + ![len + 1, 0]) ∉ K ∧ (∀ j : ℤ, (c + ![j, 1]) ∉ K) ∧
      (c + ![(-1 : ℤ), 0]) ∉ K := by
  obtain ⟨c, len, h⟩ := jc2_runFrame K hK hne
  exact ⟨c, len, h.mem, h.len_nonneg, h.isRun.run_mem, h.right_out, h.no_up, h.left_out⟩


theorem jc2_runFrame_anchored (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c len, IsExtremeCell K c ∧ jc2_RunFrame K c len := by
  obtain ⟨c, len, h⟩ := jc2_runFrame K hK hne
  exact ⟨c, len, h.isExtreme, h⟩


theorem jc2_domino_runFrame : jc2_RunFrame domino (![0, 0] : Site 2) 1 := by
  obtain ⟨hnoup, hleft, hright⟩ := jc_runFrame domino (![0, 0] : Site 2) 1 jc_domino_isTopRowRun
  exact ⟨jc_domino_isTopRowRun, hnoup, hleft, hright⟩


theorem jc2_unitCell_runFrame : jc2_RunFrame unitCell (![0, 0] : Site 2) 0 := by
  obtain ⟨hnoup, hleft, hright⟩ := jc_runFrame unitCell (![0, 0] : Site 2) 0 jc_unitCell_isTopRowRun
  exact ⟨jc_unitCell_isTopRowRun, hnoup, hleft, hright⟩

end Walls
end StatMech
