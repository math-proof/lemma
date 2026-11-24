module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
public import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex

open scoped BigOperators


noncomputable def hexColumnEmbOfPred (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) (scale : {ts : List ℤ // P ts} → ℕ) :
    HexColumnEmb (List ℤ) {ts : List ℤ // P ts} where
  wtSAW := hexSAWwt a h0 x
  emb := fun s => s.1
  emb_inj := Subtype.val_injective
  wtSAW_nn := hexSAWwt_nonneg a h0 hx
  scale := scale


end StatMech.Universality
