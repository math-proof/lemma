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
import Instance.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra
open NumberField

open scoped Quaternion
open Module


section QuaternionAlg

variable {k : Type*} [Field k] (a b : k) (ha : a ≠ 0) (hb : b ≠ 0)

/-- The reduced trace `T γ = 2 · Re γ` on the quaternion algebra `ℍ[k, a, b]`
(Definition 12.6). -/
def reducedTrace {k : Type*} [Field k] (a b : k) (γ : ℍ[k, a, b]) : k :=
  2 * γ.re

/-- The standard `k`-basis `{1, i, j, k}` of the quaternion algebra `ℍ[k, a, b]`. -/
noncomputable def basis : Basis (Fin 4) k ℍ[k, a, b] :=
  QuaternionAlgebra.basisOneIJK a 0 b

/-- The packaged `QuaternionAlgebra.Basis` structure for `ℍ[k, a, b]` itself. -/
def quatBasis : QuaternionAlgebra.Basis ℍ[k, a, b] a 0 b :=
  QuaternionAlgebra.Basis.self k

end QuaternionAlg
