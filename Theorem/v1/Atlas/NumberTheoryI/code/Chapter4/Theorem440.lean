/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/Theorem440.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.EtaleAlgebras
public import Instance.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.EtaleAlgebrasProps
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.SeparableClosure

public section

universe u v


noncomputable section EtaleAlgebraCharacterizations

open scoped TensorProduct

open EtaleAlgebra

variable (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] [Module.Finite K B]

end EtaleAlgebraCharacterizations
