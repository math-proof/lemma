/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part10
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexBetheShiftCoordinates_unshift
    {n : Nat} (N : Nat) (q : Fin (n + 1) -> Int) :
    sixVertexBetheShiftCoordinates N
      (sixVertexBetheUnshiftCoordinates N q) = q := by
  funext i
  induction i using Fin.cases with
  | zero => simp [sixVertexBetheShiftCoordinates,
      sixVertexBetheUnshiftCoordinates]
  | succ i => simp [sixVertexBetheShiftCoordinates,
      sixVertexBetheUnshiftCoordinates]

@[simp] theorem sixVertexBetheUnshiftCoordinates_shift
    {n : Nat} (N : Nat) (r : Fin (n + 1) -> Int) :
    sixVertexBetheUnshiftCoordinates N
      (sixVertexBetheShiftCoordinates N r) = r := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [sixVertexBetheUnshiftCoordinates,
      sixVertexBetheShiftCoordinates]
  | cast i => simp [sixVertexBetheUnshiftCoordinates,
      sixVertexBetheShiftCoordinates]

theorem sixVertexBetheUnshiftCoordinates_nonnegative
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x)) :
    ∀ i, 0 ≤ sixVertexBetheUnshiftCoordinates N q i := by
  intro i
  induction i using Fin.lastCases with
  | last =>
      have hq0 := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq 0
      have hxlast : 0 ≤ sixVertexSectorIntCoordinates x (Fin.last n) := by
        simp [sixVertexSectorIntCoordinates]
      simp only [sixVertexBetheUnshiftCoordinates, Fin.lastCases_last]
      have : sixVertexSectorIntCoordinates x (Fin.last n) - N ≤ q 0 := by
        simpa [sixVertexBetheShiftCoordinates] using hq0.1
      omega
  | cast i =>
      have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
      have hx : 0 ≤ sixVertexSectorIntCoordinates x i.castSucc := by
        simp [sixVertexSectorIntCoordinates]
      simp only [sixVertexBetheUnshiftCoordinates, Fin.lastCases_castSucc]
      simpa [sixVertexBetheShiftCoordinates] using hx.trans hi.1

theorem sixVertexBetheUnshiftCoordinates_strictMono
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) :
    StrictMono (sixVertexBetheUnshiftCoordinates N q) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  induction n with
  | zero => exact Fin.elim0 i
  | succ k =>
      induction i using Fin.lastCases with
      | last =>
          simpa [sixVertexBetheUnshiftCoordinates] using
            sixVertexBetheCollisionFreeTuple_wrap_lt x q hq hfree
      | cast j =>
          have hstrict := sixVertexBetheCollisionFreeTuple_strictMono
            x q hq hfree (Fin.castSucc_lt_succ (i := j.succ))
          have heq : j.castSucc.succ = j.succ.castSucc := by
            apply Fin.ext
            rfl
          rw [heq]
          simp only [sixVertexBetheUnshiftCoordinates, Fin.lastCases_castSucc]
          change q j.castSucc.succ < q j.succ.succ
          exact hstrict


end
end StatMech.FrontierD
