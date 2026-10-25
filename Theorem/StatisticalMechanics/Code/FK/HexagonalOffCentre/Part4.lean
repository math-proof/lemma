/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Def.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part6
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

theorem hexagonalTransShellEvent_increasing (R k : Nat) (x : HexVertex) :
    IsIncreasing (hexagonalTransShellEvent R k x) :=
  openCrossEvent_isIncreasing _ _ _ _

theorem hexagonalCenteredShellEvent_increasing (R k : Nat) :
    IsIncreasing (hexagonalCenteredShellEvent R k) :=
  openCrossEvent_isIncreasing _ _ _ _


theorem hexagonal_reachOpen_edgeSet_iff_openSub_reachable
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (omega : ConfigSpace H.edgeSet) (u v : W) :
    ReachOpen (fun e : H.edgeSet => e.1.out.1)
        (fun e : H.edgeSet => e.1.out.2) omega u v ↔
      (openSub H (extendActive H omega)).Reachable u v := by
  constructor
  · intro h
    induction h with
    | refl w => exact SimpleGraph.Reachable.refl w
    | @step a b c e hopen hpair _ ih =>
        have hedge : (openSub H (extendActive H omega)).Adj
            e.1.out.1 e.1.out.2 := by
          rw [openSub_adj]
          refine ⟨?_, ?_⟩
          · rw [← SimpleGraph.mem_edgeSet]
            have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
            rw [hout]
            exact e.2
          · calc
              extendActive H omega s(e.1.out.1, e.1.out.2) =
                  extendActive H omega e.1 := congrArg _ e.1.out_eq
              _ = omega e := extendActive_apply H omega e
              _ = true := hopen
        rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · rw [hU, hV] at hedge
          exact hedge.reachable.trans ih
        · rw [hU, hV] at hedge
          exact hedge.symm.reachable.trans ih
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact ReachOpen.refl u
    | @tail a b _ hab ih =>
        rw [openSub_adj] at hab
        let e : H.edgeSet := ⟨s(a, b), by
          rw [SimpleGraph.mem_edgeSet]
          exact hab.1⟩
        have hopen : omega e = true := by
          have hext := extendActive_apply H omega e
          have hopenfull : extendActive H omega s(a, b) = true := hab.2
          exact hext.symm.trans hopenfull
        have hepair :
            ((fun e : H.edgeSet => e.1.out.1) e = a ∧
              (fun e : H.edgeSet => e.1.out.2) e = b) ∨
            ((fun e : H.edgeSet => e.1.out.1) e = b ∧
              (fun e : H.edgeSet => e.1.out.2) e = a) := by
          have hout : s(e.1.out.1, e.1.out.2) = s(a, b) := e.1.out_eq
          exact Sym2.eq_iff.mp hout
        exact ih.trans (ReachOpen.step e hopen hepair (ReachOpen.refl b))

theorem hexagonal_connOpenSet_edgeSet_iff_openSub
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (omega : ConfigSpace H.edgeSet) (u : W) (B : Set W) :
    ConnOpenSet (fun e : H.edgeSet => e.1.out.1)
        (fun e : H.edgeSet => e.1.out.2) omega u B ↔
      ∃ v ∈ B, (openSub H (extendActive H omega)).Reachable u v := by
  simp only [ConnOpenSet]
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  exact reachOpen_edgeSet_iff_openSub_reachable H omega u v

end
end StatMech.FK.PeriodicPlanar
