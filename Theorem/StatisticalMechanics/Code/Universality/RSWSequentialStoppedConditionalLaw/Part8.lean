/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Structure.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcBookFaithfulTracePair.origin_mem_strictTopSet {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    origin 2 ∈ rlc_strictTopSet gamma := by
  have hn : 0 < n := by
    have hstart := gamma.1.1.2
    rw [mem_leftSide, mem_rect] at hstart
    have hneg := hfaith.right_axis_strict
    omega
  let N := n.toNat
  have hN : (N : Int) = n := Int.toNat_of_nonneg (le_of_lt hn)
  let v : Nat → Site 2 := fun k => ![0, (k : Int)]
  have hvNotPath : ∀ k : Nat, v k ∉ rlc_pathVertices gamma.1 := by
    intro k hk
    have heq := hfaith.right_axis_unique hk (by simp [v])
    have hy := congrArg (fun z : Site 2 => z 1) heq
    simp [v] at hy
    exact (not_lt_of_ge (Int.natCast_nonneg k))
      (hy ▸ hfaith.right_axis_strict)
  have hvRect : ∀ k : Nat, k ≤ N →
      v k ∈ rect 0 (2 * n) (-n) n := by
    intro k hk
    rw [mem_rect]
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hk' : (k : Int) ≤ n := by
      rw [← hN]
      exact Int.ofNat_le.mpr hk
    omega
  have hreach : ∀ k : Nat, k ≤ N →
      (rlc_rightPathAvoidGraph gamma).Reachable (v 0) (v k) := by
    intro k hk
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih =>
        have hkN : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
        have hadj : (rlc_rightPathAvoidGraph gamma).Adj (v k) (v (k + 1)) := by
          refine ⟨?_, hvRect k hkN, hvRect (k + 1) hk,
            hvNotPath k, hvNotPath (k + 1)⟩
          simp [v, hypercubicLattice_adj, Fin.sum_univ_two]
        exact (ih hkN).trans hadj.reachable
  let top : Site 2 := ![0, n]
  have htopSide : top ∈ topSide 0 (2 * n) (-n) n := by
    simp [top, mem_topSide, mem_rect, le_of_lt hn]
  have htopNot : top ∉ rlc_pathVertices gamma.1 := by
    simpa [top, v, hN] using hvNotPath N
  have htopOrigin : (rlc_rightPathAvoidGraph gamma).Reachable top (origin 2) := by
    have h := (hreach N (le_refl N)).symm
    have ht : v N = top := by
      ext i
      fin_cases i <;> simp [v, top, hN]
    have ho : v 0 = origin 2 := by
      ext i
      fin_cases i <;> simp [v, origin]
    simpa [ht, ho] using h
  exact ⟨top, htopSide, htopNot, htopOrigin⟩


theorem RlcBookFaithfulTracePair.origin_mem_strictBottomSet {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    origin 2 ∈ rlc_strictBottomSet gamma' := by
  have hn : 0 < n := by
    have hend := gamma'.1.2.1.2
    rw [mem_rightSide, mem_rect] at hend
    have hpos := hfaith.left_axis_strict
    omega
  let N := n.toNat
  have hN : (N : Int) = n := Int.toNat_of_nonneg (le_of_lt hn)
  let v : Nat → Site 2 := fun k => ![0, -(k : Int)]
  have hvNotPath : ∀ k : Nat, v k ∉ rlc_pathVertices gamma'.1 := by
    intro k hk
    have heq := hfaith.left_axis_unique hk (by simp [v])
    have hy := congrArg (fun z : Site 2 => z 1) heq
    simp [v] at hy
    exact (not_lt_of_ge (neg_nonpos.mpr (Int.natCast_nonneg k)))
      (hy ▸ hfaith.left_axis_strict)
  have hvRect : ∀ k : Nat, k ≤ N →
      v k ∈ rect (-2 * n) 0 (-n) n := by
    intro k hk
    rw [mem_rect]
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hk' : (k : Int) ≤ n := by
      rw [← hN]
      exact Int.ofNat_le.mpr hk
    omega
  have hreach : ∀ k : Nat, k ≤ N →
      (rlc_leftPathAvoidGraph gamma').Reachable (v 0) (v k) := by
    intro k hk
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih =>
        have hkN : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
        have hadj : (rlc_leftPathAvoidGraph gamma').Adj (v k) (v (k + 1)) := by
          refine ⟨?_, hvRect k hkN, hvRect (k + 1) hk,
            hvNotPath k, hvNotPath (k + 1)⟩
          simp [v, hypercubicLattice_adj, Fin.sum_univ_two]
        exact (ih hkN).trans hadj.reachable
  let bottom : Site 2 := ![0, -n]
  have hbottomSide : bottom ∈ bottomSide (-2 * n) 0 (-n) n := by
    simp [bottom, mem_bottomSide, mem_rect, le_of_lt hn]
  have hbottomNot : bottom ∉ rlc_pathVertices gamma'.1 := by
    simpa [bottom, v, hN] using hvNotPath N
  have hbottomOrigin :
      (rlc_leftPathAvoidGraph gamma').Reachable bottom (origin 2) := by
    have h := (hreach N (le_refl N)).symm
    have hb : v N = bottom := by
      ext i
      fin_cases i <;> simp [v, bottom, hN]
    have ho : v 0 = origin 2 := by
      ext i
      fin_cases i <;> simp [v, origin]
    simpa [hb, ho] using h
  exact ⟨bottom, hbottomSide, hbottomNot, hbottomOrigin⟩


end
end StatMech.Universality
