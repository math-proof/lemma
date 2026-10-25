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
import Def.v1.Atlas.Buildings.code.Valuation.LatticesValuations.Part3
open Polynomial Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

/-- *DVR closure axioms*: a packaging of the algebraic closure properties of $\mathfrak{o}
\subseteq k$ that are used throughout the development: $0, 1 \in \mathfrak{o}$, closure of
$\mathfrak{o}$ under negation, addition, and multiplication, integers are in $\mathfrak{o}$,
the inverse of a unit in $\mathfrak{o}$ is in $\mathfrak{o}$, and the determinant of any
matrix satisfying the Iwahori conditions is a unit in $\mathfrak{o}$. -/
class DVRClosure (C : DVRContext) where
  isInO_zero : C.isInO 0
  isInO_one : C.isInO 1
  isInO_neg : ∀ {x}, C.isInO x → C.isInO (-x)
  isInO_add : ∀ {x y}, C.isInO x → C.isInO y → C.isInO (x + y)
  isInO_mul : ∀ {x y}, C.isInO x → C.isInO y → C.isInO (x * y)
  isInO_intCast : ∀ (n : ℤ), C.isInO (n : C.k)
  isUnitInO_inv : ∀ {x}, C.isUnitInO x → C.isInO x⁻¹
  iwahori_det_unit : ∀ (g : Matrix (Fin C.n) (Fin C.n) C.k),
    (∀ i, C.isUnitInO (g i i)) →
    (∀ i j, i < j → C.isInO (g i j)) →
    (∀ i j, j < i → C.isInMaxIdeal (g i j)) →
    C.isUnitInO g.det

variable [DVRClosure C]


/-- *DVR topology axioms*: bundle together an ultrametric normed-field structure on $k$ and
the assertions that the valuation predicates `isInO`, `isInMaxIdeal`, `isUnitInO` correspond
to the standard normed conditions $\|x\| \le 1$, $\|x\| < 1$, $\|x\| = 1$ respectively. This
turns the algebraic DVR data into a topological one. -/
class DVRTopology where
  instNormedField : NormedField C.k
  instUltrametric : @IsUltrametricDist C.k instNormedField.toPseudoMetricSpace.toDist
  isInO_iff_norm_le_one : ∀ x : C.k,
    C.isInO x ↔ @norm C.k instNormedField.toNorm x ≤ 1
  isInMaxIdeal_iff_norm_lt_one : ∀ x : C.k,
    C.isInMaxIdeal x ↔ @norm C.k instNormedField.toNorm x < 1
  isUnitInO_iff_norm_eq_one : ∀ x : C.k,
    C.isUnitInO x ↔ @norm C.k instNormedField.toNorm x = 1

end DVRContext
