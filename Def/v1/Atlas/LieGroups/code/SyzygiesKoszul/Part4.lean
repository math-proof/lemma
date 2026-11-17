/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Structure.v1.Atlas.LieGroups.code.SyzygiesKoszul.Part2

@[expose] public section

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
