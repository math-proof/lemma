/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ActiveBoundaryDifferential
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Def.StatisticalMechanics.Code.OSSS.WiredBoxDifferential.Part5
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace WiredBoxDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open ActiveBoundaryDifferential

open FK RevealmentTranslation


theorem activeBox_crossProb_eq_wiredFull
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    FK.activeBCProbOf (boxGraph d n) (wiredBoxBoundaryGraph d n)
        (FK.betaParams (fun _ => 1) beta) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n)) =
      wiredFullCrossMass d n q beta := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    have hexp : Real.exp (-beta) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hp1 : p < 1 := by
    unfold p
    linarith [Real.exp_pos (-beta)]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hparam : FK.betaParams (fun _ : Sym2 (boxVerts d n) => (1 : Real)) beta =
      fun _ => p := by
    funext e
    simp [FK.betaParams, p]
  rw [hparam]
  simpa [wiredBoxBoundaryGraph, wiredFullCrossMass, p] using
    FK.activeBCProbOf_boundaryClique_eq_wired (boxGraph d n)
      (boxBoundary d n) hp hp1 hq0
      (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))

theorem activeBox_cross_deriv_eq_wiredFull
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    deriv (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta =
      deriv (wiredFullCrossMass d n q) beta := by
  have hevent : ∀ᶠ b in nhds beta, 0 < b := Ioi_mem_nhds hbeta
  have heq : (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) =ᶠ[nhds beta]
      wiredFullCrossMass d n q := by
    filter_upwards [hevent] with b hb
    exact activeBox_crossProb_eq_wiredFull d n q b hq hb
  exact heq.deriv_eq

theorem boxGraph_edgeSet_nonempty (d n : Nat) (hd : 1 <= d) (hn : 1 <= n) :
    Nonempty (boxGraph d n).edgeSet := by
  let j : Fin d := ⟨0, hd⟩
  let x0 : Site d := 0
  let x1 : Site d := Function.update x0 j 1
  have hx0 : x0 ∈ box d n := by
    intro i
    simp [x0]
  have hx1 : x1 ∈ box d n := by
    intro i
    by_cases hi : i = j
    · subst i
      simpa [x1, x0] using hn
    · simp [x1, x0, Function.update_of_ne hi]
  let v0 : boxVerts d n := ⟨x0, hx0⟩
  let v1 : boxVerts d n := ⟨x1, hx1⟩
  refine ⟨⟨s(v0, v1), ?_⟩⟩
  rw [SimpleGraph.mem_edgeSet]
  change (hypercubicLattice d).Adj x0 x1
  have hstep := Lattice.adj_update_succ x0 j 0
  simpa [x1, x0] using hstep

end WiredBoxDifferential
end OSSS
end StatMech
