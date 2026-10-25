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


/-- A subring `O` of a `ℚ`-algebra `A` is an order if it is finitely generated as a
`ℤ`-module and its `ℚ`-span fills `A` (cf. Definition 12.22 of "Elliptic Curves"). -/
structure IsOrder (A : Type*) [Ring A] [Algebra ℚ A] (O : Subring A) : Prop where
  fg_zmul : (O.toAddSubgroup.toIntSubmodule).FG
  span_eq_top : Submodule.span ℚ (O : Set A) = ⊤

