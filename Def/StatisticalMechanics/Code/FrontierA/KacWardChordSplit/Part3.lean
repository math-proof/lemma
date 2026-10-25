/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVisibleDiagonal
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordSplit.Part2


namespace StatMech.FrontierA

noncomputable def KWFiniteSimplePolygon.firstOfCleanChord
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    KWFiniteSimplePolygon ((j - i).val + 1) := by
  let rotated := polygon.rotate i
  have hcleanZero : rotated.ChordIsClean 0 (j - i) :=
    polygon.rotate_chordIsClean_zero hclean
  have hbound := polygon.cleanChord_distance_bounds hij hforward hbackward
  exact rotated.prefixOfCleanChord (j - i) hbound.1 hcleanZero


noncomputable def KWFiniteSimplePolygon.secondOfCleanChord
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    KWFiniteSimplePolygon ((i - j).val + 1) := by
  let rotated := polygon.rotate j
  have hcleanZero : rotated.ChordIsClean 0 (i - j) :=
    polygon.rotate_chordIsClean_zero (polygon.chordIsClean_symm hclean)
  have hbound := polygon.cleanChord_distance_bounds
    hij.symm hbackward hforward
  exact rotated.prefixOfCleanChord (i - j) hbound.1 hcleanZero

end StatMech.FrontierA
