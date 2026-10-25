/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Theorem.v1.Atlas.Buildings.code.Valuation.LatticesValuations
open Polynomial Matrix


/-- *Discrete valuation context*: a bundle of data describing a discrete valuation field. It
consists of a field $k$, an integral domain $\mathfrak{o}$ (the ring of integers), an
injective ring embedding $\mathfrak{o} \hookrightarrow k$, a chosen uniformizer
$\pi \in \mathfrak{o}$ generating the maximal ideal, and a positive integer $n$ specifying the
rank of the ambient module $k^n$ used for lattices and the building of $GL_n$. -/
structure DVRContext where
  k : Type*
  𝔬 : Type*
  [inst_field : Field k]
  [inst_comm_ring : CommRing 𝔬]
  [inst_domain : IsDomain 𝔬]
  embed : 𝔬 →+* k
  embed_injective : Function.Injective embed
  uniformizer : 𝔬
  n : ℕ
  n_pos : 0 < n

