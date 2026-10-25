/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


theorem PeriodicPlanarDualPair.MacroArrayCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.MacroArrayCertificate mu) : False := by
  let q := sheffieldMacroArrayCoordinates data.B data.T
    data.a0 data.b0 data.c0 data.d0
  let a : Nat → Nat → Real := fun n k ↦ (q n k).1
  let b : Nat → Nat → Real := fun n k ↦ (q n k).2.1
  let c : Nat → Nat → Real := fun n k ↦ (q n k).2.2.1
  let d : Nat → Nat → Real := fun n k ↦ (q n k).2.2.2
  have hspans := sheffieldMacroArrayCoordinates_spans
    data.B data.T data.increment data.a0 data.b0 data.c0 data.d0
      data.spanX0 data.spanY0
  apply D.adjacent_rectangles_contradiction_of_bounded_max_limits mu
    (B := (data.B : Real)) (by exact_mod_cast data.Bpos)
    data.primalArcBound data.dualArcBound a b c d data.K
  · simpa only [a, b, c, d, q] using hspans.1
  · simpa only [a, b, c, d, q] using hspans.2
  · simpa only [a, b, c, d, q, sheffieldMacroArrayCoordinates,
      Nat.cast_zero, mul_zero, sub_zero, add_zero] using data.verticalStart
  · simpa only [a, b, c, d, q] using data.horizontalEnd
  · intro k hk
    have hlim := data.primalAdjacent k hk
    apply hlim.congr'
    filter_upwards with n
    apply congrArg (fun x : Real ↦ x)
    congr 3
    · dsimp only [a, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
    · dsimp only [b, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
    · dsimp only [c, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
    · dsimp only [d, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
  · intro k hk
    simpa only [a, b, c, d, q] using data.dualLevels k hk


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_macroArray
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (harray :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 →
        Nonempty (D.MacroArrayCertificate mu)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  obtain ⟨data⟩ := harray hcommon
  exact data.false D _


end StatMech.FK.PeriodicPlanar
