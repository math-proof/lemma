/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFullSources
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaCurrentCopies_singletonFalse_false_false
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaCurrentCopies G sites m
      (lpReplicaSingletonFalseRowTag c) false false = {c} := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaCurrentCopies, he]

@[simp] theorem lpReplicaCurrentCopies_singletonFalse_false_true
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaCurrentCopies G sites m
      (lpReplicaSingletonFalseRowTag c) false true = ∅ := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaCurrentCopies, he]

@[simp] theorem lpReplicaCurrentCopies_singletonFalse_true_false
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaCurrentCopies G sites m
      (lpReplicaSingletonFalseRowTag c) true false =
        Finset.univ \ {c} := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaCurrentCopies, he]

@[simp] theorem lpReplicaCurrentCopies_singletonFalse_true_true
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaCurrentCopies G sites m
      (lpReplicaSingletonFalseRowTag c) true true = ∅ := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaCurrentCopies, he]

@[simp] theorem lpReplicaRowCopies_singletonFalse_false
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaRowCopies G sites m
      (lpReplicaSingletonFalseRowTag c) false = {c} := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaRowCopies, he]

@[simp] theorem lpReplicaRowCopies_singletonFalse_true
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaRowCopies G sites m
      (lpReplicaSingletonFalseRowTag c) true = Finset.univ \ {c} := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaRowCopies, he]

end
end StatMech.Ising
