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
import Structure.v1.Atlas.Buildings.code.Valuation.LatticesValuations.Part2
open Polynomial Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

/-- *Scaling a lattice by a scalar*: $\alpha \cdot \Lambda := \{\alpha \cdot w : w \in
\Lambda\}$, used to define the homothety relation between lattices. -/
def OLattice.scale (Λ : OLattice C) (α : C.k) : Set (Fin C.n → C.k) :=
  {v | ∃ w ∈ Λ.carrier, v = fun i => α * w i}

/-- *Homothety relation on lattices*: two lattices $\Lambda_1, \Lambda_2$ are *homothetic* iff
$\Lambda_1 = \alpha \cdot \Lambda_2$ for some nonzero scalar $\alpha \in k^\times$. The
quotient by this relation yields the vertices of the Bruhat--Tits building. -/
def OLattice.IsHomothetic (Λ₁ Λ₂ : OLattice C) : Prop :=
  ∃ α : C.k, α ≠ 0 ∧ Λ₁.carrier = Λ₂.scale C α

/-- *Vertex set of the Bruhat--Tits building*: the quotient of the set of $\mathfrak{o}$-lattices
in $V = k^n$ by the homothety equivalence relation. -/
def HomothetyClass := Quot (OLattice.IsHomothetic C)

end DVRContext
