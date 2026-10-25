/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part5
open Finset


namespace StatMech.FrontierD

def sixVertexRectangleStraightExtend {N M r q : ℕ}
    (z : Fin r → Bool) (ω : SixVertexRectangleArrows N M) :
    SixVertexRectangleArrows (N + r) (M + q) where
  horizontal kj :=
    Fin.addCases
      (fun j =>
        Fin.addCases (m := N) (n := r + 1)
          (fun i : Fin N => ω.horizontal (i.castSucc, j))
          (fun _ : Fin (r + 1) => ω.horizontal (Fin.last N, j)) kj.1)
      (fun _ : Fin q => false) kj.2
  vertical ik :=
    Fin.addCases
      (fun i : Fin N =>
        Fin.addCases (m := M) (n := q + 1)
          (fun j : Fin M => ω.vertical (i, j.castSucc))
          (fun _ : Fin (q + 1) => ω.vertical (i, Fin.last M)) ik.2)
      (fun i : Fin r => z i) ik.1

end StatMech.FrontierD
