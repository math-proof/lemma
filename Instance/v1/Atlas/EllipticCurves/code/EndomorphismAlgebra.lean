module
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.GroupTheory.Archimedean
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Abbrev.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra
open NumberField
open scoped Quaternion
open Module


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section QuaternionAlg

variable {k : Type*} [Field k] (a b : k) (ha : a ≠ 0) (hb : b ≠ 0)

/-- Synonym: `ℍ[k, a, b]` is a ring (recorded for use later). -/
instance : Ring ℍ[k, a, b] := inferInstance

/-- Synonym: `ℍ[k, a, b]` is a `k`-algebra. -/
instance : Algebra k ℍ[k, a, b] := inferInstance

end QuaternionAlg
