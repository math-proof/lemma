/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part14
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma fullPath_eq_pathVertex {E : Type*} {m : ℕ}
    (a b : E) (q : Fin m → E) (k : Fin (m + 2)) :
    (Fin.cons a (Fin.snoc q b) : Fin (m + 2) → E) k =
      pathVertex a b q k.val := by
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [pathVertex]
  · rw [Fin.cons_succ]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last]
      simp [pathVertex, Fin.last]
    · rw [Fin.snoc_castSucc]
      simp [pathVertex]

lemma snoc_eq_pathVertex_succ {E : Type*} {m : ℕ}
    (a b : E) (q : Fin m → E) (k : Fin (m + 1)) :
    (Fin.snoc q b : Fin (m + 1) → E) k = pathVertex a b q (k.val + 1) := by
  have h := fullPath_eq_pathVertex a b q (Fin.succ k)
  rw [Fin.cons_succ] at h
  exact h

end StatMech.FrontierB
