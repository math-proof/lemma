/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Def.StatisticalMechanics.Code.Universality.HexInjections.Part3


namespace StatMech.Universality

open Complex

open scoped BigOperators


theorem hexContourEmbOfPred_wtSAW (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) :
    (hexContourEmbOfPred a h0 hx P).wtSAW = hexSAWwt a h0 x := rfl


theorem hexContourEmbOfPred_wtContour (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) (i : {ts : List ℤ // P ts}) :
    (hexContourEmbOfPred a h0 hx P).wtContour i = hexSAWwt a h0 x i.1 := rfl


end StatMech.Universality
