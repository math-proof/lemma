/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part7
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexConnectionExponent_le_primitiveExponent {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) (x y : SixVertexSector N n) :
    sixVertexConnectionExponent hn hc x y ≤ sixVertexPrimitiveExponent N n hn hc := by
  classical
  unfold sixVertexPrimitiveExponent
  calc
    sixVertexConnectionExponent hn hc x y ≤
        ∑ z : SixVertexSector N n, sixVertexConnectionExponent hn hc x z := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
    _ ≤ ∑ w : SixVertexSector N n, ∑ z : SixVertexSector N n,
        sixVertexConnectionExponent hn hc w z := by
      exact Finset.single_le_sum (f := fun w : SixVertexSector N n =>
        ∑ z : SixVertexSector N n, sixVertexConnectionExponent hn hc w z)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)

theorem sixVertexPrimitiveExponent_pos {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) : 0 < sixVertexPrimitiveExponent N n hn hc := by
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  let x : SixVertexSector N n := Classical.choice inferInstance
  exact lt_of_lt_of_le (sixVertexConnectionExponent_pos hn hc x x)
    (sixVertexConnectionExponent_le_primitiveExponent hn hc x x)

theorem sixVertexSectorTransfer_primitivePower_pos {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) (x y : SixVertexSector N n) :
    0 < (sixVertexSectorTransfer N n c ^ sixVertexPrimitiveExponent N n hn hc) x y := by
  let k := sixVertexConnectionExponent hn hc x y
  let K := sixVertexPrimitiveExponent N n hn hc
  have hkK : k ≤ K := sixVertexConnectionExponent_le_primitiveExponent hn hc x y
  change 0 < (sixVertexSectorTransfer N n c ^ K) x y
  rw [← Nat.add_sub_of_le hkK]
  apply sixVertexSectorTransfer_mul_pos (z := y) hc.le
  · exact sixVertexConnectionExponent_entry_pos hn hc x y
  · exact sixVertexSectorTransfer_pow_self_pos hc y

theorem sixVertexSectorTransfer_isPrimitive {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) :
    (sixVertexSectorTransfer N n c).IsPrimitive :=
  ⟨sixVertexSectorTransfer_nonneg hc.le,
    sixVertexPrimitiveExponent N n hn hc,
    sixVertexPrimitiveExponent_pos hn hc,
    sixVertexSectorTransfer_primitivePower_pos hn hc⟩


end StatMech.FrontierD
