/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Algebra.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.GroupTheory.Archimedean
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Def.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra
open NumberField

open scoped Quaternion
open Module


section QuaternionAlg

/-- Convenient abbreviation for the quaternion algebra `ℍ[k, a, b]` with both
nonvanishing parameters `a, b ∈ k×`. -/
abbrev QAlgebra (k : Type*) [Field k] (a b : k) (_ : a ≠ 0) (_ : b ≠ 0) := ℍ[k, a, b]

variable {k : Type*} [Field k] (a b : k) (ha : a ≠ 0) (hb : b ≠ 0)

/-- The standard basis element `i` of the quaternion algebra `ℍ[k, a, b]`. -/
abbrev qI : ℍ[k, a, b] := ⟨0, 1, 0, 0⟩

/-- The standard basis element `j` of the quaternion algebra `ℍ[k, a, b]`. -/
abbrev qJ : ℍ[k, a, b] := ⟨0, 0, 1, 0⟩

/-- The standard basis element `k = i·j` of the quaternion algebra `ℍ[k, a, b]`. -/
abbrev qK : ℍ[k, a, b] := ⟨0, 0, 0, 1⟩

end QuaternionAlg
