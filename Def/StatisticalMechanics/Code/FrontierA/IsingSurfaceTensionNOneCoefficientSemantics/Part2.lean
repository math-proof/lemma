/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCoefficientSemantics


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

noncomputable def denseMomentWeight (X Y : Real) (index : Nat) : Real :=
  X ^ ((index / 10 : Nat) : Int) *
    Y ^ ((index % 10 : Nat) : Int)

def addRawMomentInteractions (out : List Int) (se : Nat)
    (vCount qCount : List Int) (ev eq : Nat) : List Int :=
  (List.range 10).foldl (fun out iq =>
    let coefficient := vCount.getD ev 0 * qCount.getD (10 * eq + iq) 0
    let index := 10 * (se + ev + eq) + iq
    updateCoefficient out index (fun z => z + coefficient)) out

def addRawMomentEndpoints (out : List Int) (se : Nat)
    (vCount qCount : List Int) (ev : Nat) : List Int :=
  (List.range 26).foldl (fun out eq =>
    addRawMomentInteractions out se vCount qCount ev eq) out

def addRawMomentVStates (out : List Int) (se : Nat)
    (vCount qCount : List Int) : List Int :=
  (List.range 35).foldl (fun out ev =>
    addRawMomentEndpoints out se vCount qCount ev) out

end StatMech.FrontierA.NOneSymmetricMeanCertificate
