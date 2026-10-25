/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part4
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

def radialTermEval (t : TriTerm) (r q h : Real) : Real :=
  let degree := t.ex + t.ey + t.ez
  t.coeff * r ^ t.ex * q ^ (t.ex + t.ey) *
    h ^ (degree - 3) * (1 + q + r * q) ^ (6 - degree)

def radialEvalTerms : List TriTerm -> Real -> Real -> Real -> Real
  | [], _, _, _ => 0
  | t :: ts, r, q, h => radialTermEval t r q h + radialEvalTerms ts r q h

end LowFaceCertificate
end
end StatMech.Ising
