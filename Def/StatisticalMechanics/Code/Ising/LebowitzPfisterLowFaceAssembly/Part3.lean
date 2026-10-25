/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part2
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

def radialTermCoeff (t : TriTerm) (a : Fin 13) (b : Fin 8) (c : Fin 4) : Int :=
  t.coeff * scaledBernFactor 12 27720 t.ex a *
    scaledBernFactor 7 105 t.ey b * scaledBernFactor 3 3 t.ez c

def radialCoeffTerms : List TriTerm -> Fin 13 -> Fin 8 -> Fin 4 -> Int
  | [], _, _, _ => 0
  | t :: ts, a, b, c => radialTermCoeff t a b c + radialCoeffTerms ts a b c

end LowFaceCertificate
end
end StatMech.Ising
