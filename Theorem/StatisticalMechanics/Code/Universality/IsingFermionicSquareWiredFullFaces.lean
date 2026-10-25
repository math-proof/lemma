/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareWedgeFaceKey_open_localMate
    (n : Nat) (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWedgeFaceKey n
        (FKIsingMedialDart.localMate
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) d) =
      fkIsingSquareWedgeFaceKey n d := by
  rcases d with ⟨e, side⟩
  have hopen : FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset e.1 = true := by
    rw [FK.edgeSetConfig_apply]
    exact SimpleGraph.mem_edgeFinset.mpr e.2
  have hstep := (fkIsingSquareOrientedEdge n e).step
  cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
    cases side <;>
    simp only [FKIsingMedialDart.localMate] <;>
    rw [show FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset e.1 = true from hopen] <;>
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis] at hstep ⊢
  all_goals
    have h0 := congrFun hstep 0
    have h1 := congrFun hstep 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one] at h0 h1
    constructor <;> omega

set_option maxHeartbeats 2000000 in
theorem fkIsingSquareWedgeFaceKey_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hdint : fkIsingSquareInteriorFaceKey n
      (fkIsingSquareWedgeFaceKey n d)) :
    fkIsingSquareWedgeFaceKey n (fkIsingSquareBondMate n hn d) =
      fkIsingSquareWedgeFaceKey n d := by
  let u := fkIsingSquareDartEndpoint n d
  let q := fkIsingSquareDartDirection n d
  let hq := fkIsingSquareDartDirection_available n d
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases ht : (fkIsingSquareSideCorner d.2).2 <;>
    cases hqdir : q <;>
    by_cases hE : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hN : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hW : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hS : fkIsingSquareDirectionAvailable n u .south <;>
    have hE' := hE <;>
    have hN' := hN <;>
    have hW' := hW <;>
    have hS' := hS <;>
    simp [fkIsingSquareDirectionAvailable, u] at hE' hN' hW' hS' <;>
    simp [fkIsingSquareDirectionAvailable, u, q, hqdir] at hq <;>
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareInteriorFaceKey,
      u, q, ht, hqdir] at hdint <;>
    simp [u] at b0 b1 <;>
    simp [fkIsingSquareBondMate, fkIsingSquareWedgeFaceKey,
      fkIsingSquareNextDirection, fkIsingSquarePreviousDirection,
      u, q, ht, hqdir, hE, hN, hW, hS] <;>
    omega

theorem fkIsingSquareWiredBoundaryDart_faceKey_not_interior
    (n : Nat) (hn : 0 < n)
    (i : FKIsingSquareWiredBoundaryDartIndex n) :
    ¬ fkIsingSquareInteriorFaceKey n
      (fkIsingSquareWedgeFaceKey n
        (fkIsingSquareWiredBoundaryDart n hn i)) := by
  cases i <;>
    simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareLeftVerticalLower,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareMarkedA,
      fkIsingSquareMarkedB]

theorem fkIsingSquareWiredBondMate_eq_bondMate_of_interior
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : fkIsingSquareInteriorFaceKey n
      (fkIsingSquareWedgeFaceKey n d)) :
    fkIsingSquareWiredBondMate n hn d = fkIsingSquareBondMate n hn d := by
  let sigma := fkIsingSquareWiredShiftDartEquiv n hn
  have hdout : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, rfl⟩
    exact fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn i hd
  have hBout : fkIsingSquareBondMate n hn d ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, hi⟩
    have hinter : fkIsingSquareInteriorFaceKey n
        (fkIsingSquareWedgeFaceKey n (fkIsingSquareBondMate n hn d)) := by
      rw [fkIsingSquareWedgeFaceKey_bondMate n hn d hd]
      exact hd
    rw [← hi] at hinter
    exact fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn i hinter
  have hfix : sigma d = d :=
    Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hdout
  have hfix' : sigma.symm d = d := by
    calc
      sigma.symm d = sigma.symm (sigma d) := congrArg sigma.symm hfix.symm
      _ = d := sigma.symm_apply_apply d
  have hBfix : sigma (fkIsingSquareBondMate n hn d) =
      fkIsingSquareBondMate n hn d :=
    Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hBout
  simp only [fkIsingSquareWiredBondMate,
    fkIsingSquareWiredBondMateEquiv, Equiv.Perm.mul_apply]
  rw [show (fkIsingSquareWiredShiftDartEquiv n hn).symm d = d by exact hfix']
  exact hBfix

end
end StatMech.Universality
