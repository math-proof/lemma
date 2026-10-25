/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part10


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


open HexWalk


def HexWalk.StaysIn (inRegion : ℂ → Prop) (w : HexWalk) : Prop :=
  ∀ m ∈ w.mids, inRegion m


def HexWalk.EndsAt (z : ℂ) (w : HexWalk) : Prop := w.endMid = z


noncomputable def parafSummand (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (σ x : ℝ) (ts : List ℤ) : ℂ :=
  haveI := Classical.propDecidable ((ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z)
  if (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z then
    Complex.exp (-Complex.I * (σ : ℂ) * ((ofTurns a h0 ts).turning : ℂ))
      * ((x : ℂ) ^ (ofTurns a h0 ts).numVertices)
  else 0


noncomputable def parafObservable (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (σ x : ℝ) : ℂ :=
  ∑' ts : List ℤ, parafSummand inRegion a h0 z σ x ts


def IsBoundaryOf (boundary region : ℂ → Prop) : Prop := ∀ m, boundary m → region m


end StatMech.Universality
