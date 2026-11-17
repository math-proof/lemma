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
public import Structure.v1.Atlas.AlgebraicCombinatorics.code.CirculantHadamard

@[expose] public section

open Complex NumberField

variable {n : ℕ} [NeZero n]


noncomputable def CirculantHadamardMatrix.eigenvalue (H : CirculantHadamardMatrix n)
    (ζ : ℂ) (j : ZMod n) : ℂ :=
  ∑ i : ZMod n, (H.a i : ℂ) * ζ ^ (i * j).val

def CirculantHadamardMatrix.toMatrix (H : CirculantHadamardMatrix n) :
    Matrix (ZMod n) (ZMod n) ℤ :=
  Matrix.of fun i j => H.a (i - j)

noncomputable def eigenvalueOI {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K]
    (H : CirculantHadamardMatrix n) (ζ_int : 𝓞 K) (j : ZMod n) : 𝓞 K :=
  ∑ i : ZMod n, algebraMap ℤ (𝓞 K) (H.a i) * ζ_int ^ (i * j).val

