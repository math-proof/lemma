/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/CirculantHadamard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.Data.Real.Sqrt
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public section

open Complex NumberField


structure CirculantHadamardMatrix (n : ℕ) [NeZero n] where
  a : ZMod n → ℤ
  entries_sq : ∀ i, a i ^ 2 = 1
  orthogonality : ∀ j : ZMod n, ∑ i : ZMod n, a i * a (i + j) = if j = 0 then (n : ℤ) else 0

