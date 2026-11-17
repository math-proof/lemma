/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.Tactic.LinearCombination
public import Theorem.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part2
public section

open Polynomial

variable {E : ShortWeierstrassCurve k}


/-- Input data for *Vélu's odd-degree* isogeny construction: a finite set
$\{Q_1, \dots, Q_n\}$ of affine points (representatives modulo $\pm$), such
that the resulting kernel has odd order $n + 1$ (i.e.\ the cardinality of `pts`
plus one is odd). -/
structure VeluOddData (E : ShortWeierstrassCurve k) where
  pts : Finset (AffinePoint E)
  odd_order : Odd (pts.card + 1)

