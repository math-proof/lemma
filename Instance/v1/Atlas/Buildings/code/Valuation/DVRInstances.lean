/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Theorem.v1.Atlas.Buildings.code.Valuation.DVRInstances.Part2
open DVRContext

variable (p : ℕ) [Fact (Nat.Prime p)]


noncomputable section

set_option maxHeartbeats 32000000

variable {p} (n : ℕ) (hn : 0 < n)

/-- *`DVRClosure` instance for the $p$-adic context*: assembles all closure properties of
$\mathbb{Z}_p$ inside $\mathbb{Q}_p$ — closed under $0$, $1$, negation, addition,
multiplication, integer casts, and inverses of units; plus Iwahori-determinant unit. -/
instance padicDVRClosure : DVRClosure (padicDVRContext p n hn) where
  isInO_zero := ⟨0, rfl⟩
  isInO_one := ⟨1, rfl⟩
  isInO_neg := fun {x} ⟨r, hr⟩ => ⟨-r, by subst hr; rfl⟩
  isInO_add := fun {x y} ⟨r, hr⟩ ⟨s, hs⟩ => ⟨r + s, by subst hr; subst hs; rfl⟩
  isInO_mul := fun {x y} ⟨r, hr⟩ ⟨s, hs⟩ => ⟨r * s, by subst hr; subst hs; rfl⟩
  isInO_intCast := fun m => ⟨(m : ℤ_[p]), by norm_cast⟩
  isUnitInO_inv := fun {x} hx => by
    have hx' := (padic_isUnitInO_iff n hn x).mp hx
    exact (padic_isInO_iff n hn x⁻¹).mpr (by simp [norm_inv, hx'])
  iwahori_det_unit := padic_iwahori_det_unit n hn

/-- *`DVRTopology` instance for the $p$-adic context*: equips the $p$-adic DVR context with
its norm topology (a `NormedField`) and the ultrametric inequality, registering the
norm-characterisations of `isInO`, `isInMaxIdeal`, and `isUnitInO`. -/
instance padicDVRTopology : DVRContext.DVRTopology (padicDVRContext p n hn) where
  instNormedField := inferInstanceAs (NormedField ℚ_[p])
  instUltrametric := Padic.instIsUltrametricDist p
  isInO_iff_norm_le_one := padic_isInO_iff n hn
  isInMaxIdeal_iff_norm_lt_one := padic_isInMaxIdeal_iff n hn
  isUnitInO_iff_norm_eq_one := padic_isUnitInO_iff n hn

end
