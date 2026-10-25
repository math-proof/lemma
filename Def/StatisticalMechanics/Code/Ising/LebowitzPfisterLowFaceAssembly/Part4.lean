/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part3
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

def bernsteinEvalTerms (ts : List TriTerm) (r q h : Real) : Real :=
  ∑ a : Fin 13, ∑ b : Fin 8, ∑ c : Fin 4,
    (radialCoeffTerms ts a b c : Real) *
      bernsteinWeight 12 a r * bernsteinWeight 7 b q * bernsteinWeight 3 c h

end LowFaceCertificate
end
end StatMech.Ising
