/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/Theorem440.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Nat.Atlas.v1.NumberTheoryI.code.EtaleAlgebras
import sympy.atlas.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.EtaleAlgebrasProps
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SeparableClosure

universe u v

noncomputable section EtaleAlgebraCharacterizations

open scoped TensorProduct
open EtaleAlgebra

variable (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] [Module.Finite K B]
