/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Class.v1.Atlas.AlgebraicGeometryI.code.DegreeFormula
set_option maxHeartbeats 800000

open Ideal Module


/-- The degree of the ramification divisor over a finite set `S` of primes of `A`,
defined as `∑_{𝔭 ∈ S} ∑_{𝔔 ∣ 𝔭} (e(𝔔/𝔭) - 1)`. -/
noncomputable def degRamificationDivisor
    {A : Type*} {B : Type*}
    [CommRing A] [CommRing B]
    [IsDedekindDomain B]
    [Algebra A B]
    (S : Finset (Ideal A)) : ℤ :=
  ↑(S.sum (fun 𝔭 => (primesOverFinset 𝔭 B).sum (fun 𝔔 => 𝔭.ramificationIdx 𝔔 - 1)))

