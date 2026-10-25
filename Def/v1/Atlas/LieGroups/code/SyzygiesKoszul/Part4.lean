/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Structure.v1.Atlas.LieGroups.code.SyzygiesKoszul.Part2


noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial

variable (k : Type*) [Field k] (n : ℕ)

local notation "R" => MvPolynomial (Fin n) k

def freeModuleGrading (d : ℕ) :
    Submodule k (Fin m → MvPolynomial (Fin n) k) where
  carrier := {f | ∀ i, f i ∈ homogeneousSubmodule (Fin n) k d}
  zero_mem' i := (homogeneousSubmodule (Fin n) k d).zero_mem
  add_mem' ha hb i := (homogeneousSubmodule (Fin n) k d).add_mem (ha i) (hb i)
  smul_mem' c _ ha i := (homogeneousSubmodule (Fin n) k d).smul_mem c (ha i)

def twistedFreeModuleGrading {m : ℕ} (degrees : Fin m → ℕ) (p : ℕ) :
    Submodule k (Fin m → MvPolynomial (Fin n) k) where
  carrier := {f | ∀ j, f j ∈ homogeneousSubmodule (Fin n) k (p - degrees j)}
  zero_mem' j := (homogeneousSubmodule (Fin n) k (p - degrees j)).zero_mem
  add_mem' ha hb j := (homogeneousSubmodule (Fin n) k (p - degrees j)).add_mem (ha j) (hb j)
  smul_mem' c _ ha j := (homogeneousSubmodule (Fin n) k (p - degrees j)).smul_mem c (ha j)


end
