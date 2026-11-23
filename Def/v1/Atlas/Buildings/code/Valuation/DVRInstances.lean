/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
public import Theorem.Nat.IsInO
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Theorem.v1.Atlas.Buildings.code.Valuation.DVRInstances

@[expose] public section

open DVRContext

variable (p : ℕ) [Fact (Nat.Prime p)]


noncomputable section

set_option maxHeartbeats 32000000

/-- *The $p$-adic DVR context*: instantiates the `DVRContext` framework with $k = \mathbb{Q}_p$,
$\mathfrak{o} = \mathbb{Z}_p$, the natural inclusion as embed, and the uniformizer $p$. The
parameter $n$ records the relevant dimension (e.g. of an Iwahori subgroup of $GL_n$). -/
def padicDVRContext (n : ℕ) (hn : 0 < n) : DVRContext where
  k := ℚ_[p]
  𝔬 := ℤ_[p]
  embed := (PadicInt.subring p).subtype
  embed_injective := Subtype.coe_injective
  uniformizer := (p : ℤ_[p])
  n := n
  n_pos := hn

end
