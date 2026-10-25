/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Structure.StatisticalMechanics.Code.Walls.jc_toprowrun
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc_extremeCell_topRowRun (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) : jc_TopRowRun K c (jc_runMax K c) where
  isExtreme := hc
  run_mem := jc_runMax_mem K hK c hc.mem
  run_maximal := jc_runMax_succ_nmem_K K hK c hc.mem
  run_topRow := fun j => jc_shiftX_coord1 c (j : ℤ)
  topRow_maximal := fun v hv => by
    by_contra h
    rw [not_le] at h
    exact extremeCell_not_mem_of_higher K c v hc h hv
  leftMost := by
    have hnmem := extremeCell_head_nmem K c hc
    rw [leftDart_head] at hnmem
    have hshift : jc_shiftX c (-1) = c + ![-1, 0] := by rw [jc_shiftX]
    rw [hshift]
    exact hnmem


theorem jc_topRowRun_of_earAnchor (K : Set (Site 2)) (hK : K.Finite) {c : Site 2}
    (hanchor : jc_EarAnchor K c) : jc_TopRowRun K c (jc_runMax K c) :=
  jc_extremeCell_topRowRun K hK c hanchor.isExtreme


theorem jc_topRowRun (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c L, jc_TopRowRun K c L := by
  obtain ⟨c, hanchor⟩ := jc_earAnchor K hK hne
  exact ⟨c, jc_runMax K c, jc_topRowRun_of_earAnchor K hK hanchor⟩


theorem jc_topRowRun_explicit (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c L, c ∈ K ∧ (∀ j : ℕ, j ≤ L → jc_shiftX c (j : ℤ) ∈ K) ∧
      jc_shiftX c ((L : ℤ) + 1) ∉ K ∧ (∀ j : ℕ, (jc_shiftX c (j : ℤ)) 1 = c 1) ∧
      (∀ v ∈ K, v 1 ≤ c 1) ∧ jc_shiftX c (-1) ∉ K := by
  obtain ⟨c, L, hrun⟩ := jc_topRowRun K hK hne
  exact ⟨c, L, hrun.isExtreme.mem, hrun.run_mem, hrun.run_maximal, hrun.run_topRow,
    hrun.topRow_maximal, hrun.leftMost⟩


theorem jc_unitCell_topRowRun : ∃ c L, jc_TopRowRun unitCell c L :=
  jc_topRowRun unitCell unitCell_finite ⟨_, origin_mem_unitCell⟩

end Walls
end StatMech
