/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorProfileCount.Part2
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.FluxEdgeCopy


section SigmaPi

variable {E : Type*} [Fintype E] [DecidableEq E]
  {gamma : E -> Type*} [forall e, Fintype (gamma e)]
  [forall e, DecidableEq (gamma e)]

noncomputable def grahamFourColorProfile
    (c : GrahamFourColoring (Sigma fun e : E => gamma e)) :
    (E -> Nat) × (E -> Nat) × (E -> Nat) :=
  (fun e => #(sigmaFinsetEquivPi c.color1 e),
    fun e => #(sigmaFinsetEquivPi c.color2 e),
    fun e => #(sigmaFinsetEquivPi c.color3 e))


end SigmaPi
end StatMech.FrontierA
