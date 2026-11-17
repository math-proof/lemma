/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Def.v1.Atlas.Buildings.code.Valuation.LatticesValuations.Part2
public section

open Polynomial Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

/-- *Primitive lattice with a bilinear form*: an $\mathfrak{o}$-lattice $\Lambda$ equipped with
a bilinear form `form` $: V \times V \to k$ such that the form is integral on $\Lambda$
(takes values in $\mathfrak{o}$) and is nondegenerate modulo $\pi$: any element $v \in
\Lambda$ that is not divisible by the uniformizer pairs to a unit against some element of
$\Lambda$. -/
structure PrimitiveLattice extends OLattice C where
  form : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k
  form_linear_left : ∀ (r : C.k) (v w : Fin C.n → C.k),
    form (r • v) w = r * form v w
  form_linear_right : ∀ (r : C.k) (v w : Fin C.n → C.k),
    form v (r • w) = r * form v w
  form_integral : ∀ {v w}, v ∈ carrier → w ∈ carrier → C.isInO (form v w)
  form_nondeg : ∀ {v}, v ∈ carrier →
    (¬ ∃ w ∈ carrier, v = C.oscal C.uniformizer w) →
    ∃ w ∈ carrier, C.isUnitInO (form v w)


end DVRContext
