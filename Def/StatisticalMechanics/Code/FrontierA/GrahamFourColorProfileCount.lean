/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorProfileCount
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.FluxEdgeCopy


section SigmaPi

variable {E : Type*} [Fintype E] [DecidableEq E]
  {gamma : E -> Type*} [forall e, Fintype (gamma e)]
  [forall e, DecidableEq (gamma e)]

noncomputable def grahamFourColorSigmaEquivPi :
    GrahamFourColoring (Sigma fun e : E => gamma e) ≃
      (forall e : E, GrahamFourColoring (gamma e)) where
  toFun c := fun e =>
    { color1 := sigmaFinsetEquivPi c.color1 e
      color2 := sigmaFinsetEquivPi c.color2 e
      color3 := sigmaFinsetEquivPi c.color3 e }
  invFun c :=
    { color1 := sigmaFinsetEquivPi.symm (fun e => (c e).color1)
      color2 := sigmaFinsetEquivPi.symm (fun e => (c e).color2)
      color3 := sigmaFinsetEquivPi.symm (fun e => (c e).color3) }
  left_inv c := by
    cases c
    simp only [GrahamFourColoring.mk.injEq]
    constructor
    · rw [← Equiv.eq_symm_apply]
      rfl
    constructor <;> · rw [← Equiv.eq_symm_apply]; rfl
  right_inv c := by
    funext e
    cases h : c e
    simp only [Equiv.apply_symm_apply]
    rw [h]

end SigmaPi
end StatMech.FrontierA
