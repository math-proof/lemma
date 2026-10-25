/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaReflectedResidual_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaReflectedResidual G sites
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
        (fun e => a (lpReplicaCurrentEdgeReflect G sites e)) =
      fun e => lpReplicaReflectedResidual G sites m a
        (lpReplicaCurrentEdgeReflect G sites e) := by
  funext e
  unfold lpReplicaReflectedResidual
  dsimp only

set_option maxHeartbeats 800000 in


theorem lpReplicaRowFiberMass_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaRowFiberMass G sites beta J hf r
        (A.map lpReplicaCurrentReflect.toEmbedding)
        (B.map lpReplicaCurrentReflect.toEmbedding)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) =
      lpReplicaRowFiberMass G sites beta J hf r A B m := by
  classical
  let Q := lpReplicaSubprofileReflectEquiv G sites m
  unfold lpReplicaRowFiberMass
  symm
  apply Fintype.sum_equiv Q
  intro a
  change lpReplicaDisconnProfileTerm G sites beta J hf r A a.1 *
      lpReplicaDisconnProfileTerm G sites beta J hf r B
        (lpReplicaReflectedResidual G sites m a.1) =
    lpReplicaDisconnProfileTerm G sites beta J hf r
        (A.map lpReplicaCurrentReflect.toEmbedding)
        (fun e => a.1 (lpReplicaCurrentEdgeReflect G sites e)) *
      lpReplicaDisconnProfileTerm G sites beta J hf r
        (B.map lpReplicaCurrentReflect.toEmbedding)
        (lpReplicaReflectedResidual G sites
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (fun e => a.1 (lpReplicaCurrentEdgeReflect G sites e)))
  rw [lpReplicaDisconnProfileTerm_reflect,
    lpReplicaReflectedResidual_reflect,
    lpReplicaDisconnProfileTerm_reflect]


theorem lpReplicaProfileOrbitMass_reflectSources
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaProfileOrbitMass G sites beta J hf r
        (A.map lpReplicaCurrentReflect.toEmbedding)
        (B.map lpReplicaCurrentReflect.toEmbedding) q =
      lpReplicaProfileOrbitMass G sites beta J hf r A B q := by
  classical
  rw [lpReplicaProfileOrbitMass_eq_sum,
    lpReplicaProfileOrbitMass_eq_sum]
  symm
  apply Fintype.sum_equiv (lpReplicaProfileOrbitReflectEquiv G sites q)
  intro m
  exact (lpReplicaRowFiberMass_reflect G sites beta J hf r A B m.1).symm


theorem lpReplicaCurrentReflect_seamSource
    (G : SimpleGraph V) (sites : I -> V) (i : I) :
    (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i).map
      lpReplicaCurrentReflect.toEmbedding =
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i := by
  let R := lpReplicaCurrent_reflectedMatchingCut G
    (fun _ => 0) (fun _ => 0) sites 0
  simpa [lpReflectSource, R] using lpReflectSource_seam R i


theorem lpReplicaCurrentReflect_ghostSource
    (G : SimpleGraph V) (sites : I -> V) :
    (lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1).map lpReplicaCurrentReflect.toEmbedding =
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1 := by
  let R := lpReplicaCurrent_reflectedMatchingCut G
    (fun _ => 0) (fun _ => 0) sites 0
  simpa [lpReflectSource, R] using lpReflectSource_ghost R


theorem lpReplicaCurrentReflect_offdiagSource
    (G : SimpleGraph V) (sites : I -> V) (i j : I) :
    (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1).map
        lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
  let R := lpReplicaCurrent_reflectedMatchingCut G
    (fun _ => 0) (fun _ => 0) sites 0
  simpa [lpReflectSource, R] using
    lpReflectSource_matchingCommonSource R i j


end
end StatMech.Ising
