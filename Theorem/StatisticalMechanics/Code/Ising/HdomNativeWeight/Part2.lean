/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.BackboneExists
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part2
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem hnw_noneConn_not_allConn (m : Current V) {o x y : V}
    (h : hnw_noneConn G m o x y) : ¬ hnw_allConn G m o x y := by
  rintro ⟨hxy, _, _⟩
  exact h.1 (connOdd_imp_connPos G.edgeFinset m hxy)


theorem hnw_switching (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    {u v : V} (huv : u ≠ v) (hconn : connP (oddEdges G.edgeFinset m) u v) (A : Finset V) :
    hnw_mass G β J m (A ∆ {u, v}) = hnw_mass G β J m A :=
  ising_switching_weighted G β J m huv hconn 1 A


theorem hnw_mass_vanish (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V) (hm : Sharpness.sources G m = A)
    {u v : V} (huv : u ≠ v) (hdisc : ¬ connP (posEdges G.edgeFinset m) u v) :
    hnw_mass G β J m (A ∆ {u, v}) = 0 :=
  ising_switching_weighted_vanishing G β J m hnd A hm huv hdisc 1


theorem hnw_conn_trans_xy (m : Current V) {o x y : V}
    (hoy : connP (oddEdges G.edgeFinset m) o y) (hox : connP (oddEdges G.edgeFinset m) o x) :
    connP (oddEdges G.edgeFinset m) x y :=
  Relation.ReflTransGen.trans (connP_symm _ hox) hoy


theorem hnw_conn_trans_ox (m : Current V) {o x y : V}
    (hxy : connP (oddEdges G.edgeFinset m) x y) (hoy : connP (oddEdges G.edgeFinset m) o y) :
    connP (oddEdges G.edgeFinset m) o x :=
  Relation.ReflTransGen.trans hoy (connP_symm _ hxy)


theorem hnw_conn_trans_oy (m : Current V) {o x y : V}
    (hxy : connP (oddEdges G.edgeFinset m) x y) (hox : connP (oddEdges G.edgeFinset m) o x) :
    connP (oddEdges G.edgeFinset m) o y :=
  Relation.ReflTransGen.trans hox hxy


theorem hnw_gap_allConn (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : hnw_allConn G m o x y) :
    hnw_gap G β J m A o x y = -2 * hnw_mass G β J m A := by
  obtain ⟨hxy', hoy', hox'⟩ := hall
  unfold hnw_gap
  rw [hnw_switching G β J m hxy hxy' A, hnw_switching G β J m hoy hoy' A,
      hnw_switching G β J m hox hox' A]
  ring


theorem hnw_gap_noneConn (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V) (hm : Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hnone : hnw_noneConn G m o x y) :
    hnw_gap G β J m A o x y = hnw_mass G β J m A := by
  obtain ⟨hxy', hoy', hox'⟩ := hnone
  unfold hnw_gap
  rw [hnw_mass_vanish G β J m hnd A hm hxy hxy',
      hnw_mass_vanish G β J m hnd A hm hoy hoy',
      hnw_mass_vanish G β J m hnd A hm hox hox']
  ring


end Ising
end StatMech
