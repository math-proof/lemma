/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorMaskMatching.Part2
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def leftRowDataMaskSigmaEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W) :
    leftRowData ends m j k l zero ≃
      Sigma (leftMaskFiber ends m j k l zero) :=
  (leftFiberEquivRowData ends m j k l zero).symm.trans
    (Equiv.sigmaFiberEquiv
      (fun c : leftFiber ends m {j, k} {k, l} k zero =>
        fourColorMaskProfile m c.1)).symm


noncomputable def rightRowDataMaskSigmaEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W) :
    Sigma (rightMaskFiber ends m j k l zero) ≃
      rightRowData ends m j k l zero :=
  (Equiv.sigmaFiberEquiv
      (fun c : rightFiber ends m {j, k} {k, l} k zero =>
        fourColorMaskProfile m c.1)).trans
    (rightFiberEquivRowData ends m j k l zero)


noncomputable def rowDataRepairEmbedding_of_maskFiberEmbeddings
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero) :
    leftRowData ends m j k l zero ↪ rightRowData ends m j k l zero where
  toFun d :=
    let c := rowDataToLeftFiber ends m j k l zero d
    let p := fourColorMaskProfile m c.1
    rightFiberToRowData ends m j k l zero (f p ⟨c, rfl⟩).1
  inj' := by
    intro d e hde
    let c := rowDataToLeftFiber ends m j k l zero d
    let q := rowDataToLeftFiber ends m j k l zero e
    let pc := fourColorMaskProfile m c.1
    let pq := fourColorMaskProfile m q.1
    let fc := f pc ⟨c, rfl⟩
    let fq := f pq ⟨q, rfl⟩
    have hright : fc.1 = fq.1 := by
      have h := congrArg (rowDataToRightFiber ends m j k l zero) hde
      simpa [c, q, pc, pq, fc, fq,
        rowDataToRightFiber_leftInverse] using h
    have hp : pc = pq := by
      calc
        pc = fourColorMaskProfile m fc.1.1 := fc.2.symm
        _ = fourColorMaskProfile m fq.1.1 :=
          congrArg (fun x : rightFiber ends m {j, k} {k, l} k zero =>
            fourColorMaskProfile m x.1) hright
        _ = pq := fq.2
    let sc : Sigma (leftMaskFiber ends m j k l zero) := ⟨pc, ⟨c, rfl⟩⟩
    let sq : Sigma (leftMaskFiber ends m j k l zero) := ⟨pq, ⟨q, rfl⟩⟩
    let sf := (Function.Embedding.refl (Finset I × Finset I)).sigmaMap f
    have hsout : sf sc = sf sq := by
      apply Sigma.subtype_ext hp
      simpa [sf, sc, sq, fc, fq] using hright
    have hsin : sc = sq := sf.injective hsout
    have hcq : c = q := congrArg
      (fun x : Sigma (leftMaskFiber ends m j k l zero) => x.2.1) hsin
    exact rowDataToLeftFiber_injective ends m j k l zero hcq


end StatMech.GrahamGHS.FourColor
