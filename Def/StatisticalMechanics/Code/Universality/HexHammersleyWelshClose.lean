/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexHammersleyWelshClose


namespace StatMech.Universality

open scoped BigOperators


noncomputable def hhw_hexColumnOfBoundary (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop)
    (hreach : ∀ ts, mem ts →
      ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re)
    (lam tau : Finset {ts : List ℤ // mem ts} → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hbdry : ∀ s : Finset {ts : List ℤ // mem ts},
      hexCl * lam s + hexCt * tau s
        + (∑ w ∈ s, hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices) = 1) :
    HexColumn T hexChiE :=
  hexColumnOfWidth a h0 T hexChiE mem hreach
    (hhw_critSummable_of_boundary
      (fun w : {ts : List ℤ // mem ts} => hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices)
      hexCl hexCt (le_of_lt hexCl_pos) (le_of_lt hexCt_pos)
      lam tau hlam htau (fun _ => pow_nonneg (le_of_lt hexChiE_pos) _) hbdry)
    (hhw_critLeOne_of_boundary
      (fun w : {ts : List ℤ // mem ts} => hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices)
      hexCl hexCt (le_of_lt hexCl_pos) (le_of_lt hexCt_pos)
      lam tau hlam htau (fun _ => pow_nonneg (le_of_lt hexChiE_pos) _) hbdry)


end StatMech.Universality
