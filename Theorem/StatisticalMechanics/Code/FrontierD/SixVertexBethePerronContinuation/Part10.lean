/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part10
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorGap_pos_of_noAdjacent
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (i : Fin n) :
    0 < sixVertexSectorGap x i := by
  rw [sixVertexSectorGap]
  split_ifs with hnext
  · have hgap := hx.1 i.val hnext
    have hi : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
    rw [hi] at hgap
    omega
  · have hn : 0 < n := Nat.pos_of_ne_zero
      (fun hn => by subst n; exact Fin.elim0 i)
    have hilast : i.val = n - 1 := by omega
    have hwrap := hx.2 hn
    have hi : (⟨n - 1, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      simpa using hilast.symm
    rw [hi] at hwrap
    omega


end
end StatMech.FrontierD
