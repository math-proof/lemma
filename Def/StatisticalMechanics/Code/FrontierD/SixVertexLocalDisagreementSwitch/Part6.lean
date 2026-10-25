/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part4
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexRectangleSwitchFirst
    (mask omega eta : SixVertexRectangleArrows N M) :
    SixVertexRectangleArrows N M where
  horizontal e := if mask.horizontal e then eta.horizontal e
    else omega.horizontal e
  vertical e := if mask.vertical e then eta.vertical e
    else omega.vertical e


def sixVertexRectangleSwitchSecond
    (mask omega eta : SixVertexRectangleArrows N M) :
    SixVertexRectangleArrows N M where
  horizontal e := if mask.horizontal e then omega.horizontal e
    else eta.horizontal e
  vertical e := if mask.vertical e then omega.vertical e
    else eta.vertical e


def sixVertexRectangleLocalSwitchMask
    (mask : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    SixVertexLocalIncomingPattern :=
  ![mask.horizontal (v.1.castSucc, v.2),
    mask.horizontal (v.1.succ, v.2),
    mask.vertical (v.1, v.2.castSucc),
    mask.vertical (v.1, v.2.succ)]


def sixVertexLocalSwapMask
    (p q mask : SixVertexLocalIncomingPattern) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  (fun i => if mask i then q i else p i,
    fun i => if mask i then p i else q i)


def sixVertexLocalSwitchMaskCount
    (mask : SixVertexLocalIncomingPattern) : Nat :=
  ∑ i, (mask i).toNat


end
end StatMech.FrontierD
