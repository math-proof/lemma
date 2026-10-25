/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hexW1Exit_singleton_straightSide (a : ℂ) (h0 : ℤ) :
    HexStraightSide (fun m => m = a) (fun m => m = a + HexWalk.halfStep h0) a h0 a where
  H := h0 + 3
  uniqueInterior := fun h hint => hexW1Exit_singleton_uniqueInterior a h0 h hint
  interiorVertices := by
    intro ts hadm v hv hvne
    
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    
    rw [hexInfra_headAccum_nil] at hvne
    have hverts : (HexWalk.ofTurns a h0 ([] : List ℤ)).vertices = [a + HexWalk.halfStep h0] := by
      unfold HexWalk.ofTurns HexWalk.vertices; simp [HexWalk.verticesAux]
    rw [hverts, List.mem_singleton] at hv
    exact absurd hv hvne


end StatMech.Universality
