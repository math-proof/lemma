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
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part2


namespace StatMech.Universality

open Complex

open scoped BigOperators


noncomputable def hexContourEmbOfPred (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) :
    HexContourEmb (List ℤ) {ts : List ℤ // P ts} where
  wtSAW := hexSAWwt a h0 x
  emb := fun s => s.1
  emb_inj := Subtype.val_injective
  wtSAW_nn := hexSAWwt_nonneg a h0 hx


end StatMech.Universality
