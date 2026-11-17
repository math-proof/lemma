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
public import Abbrev.v1.Atlas.Buildings.code.Valuation.LatticesValuations

@[expose] public section

open Polynomial Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

/-- *Upper unipotent subgroup of $GL_n(k)$*: matrices with $1$'s on the diagonal and zeros
strictly below the diagonal. -/
def UpperUnipotent : Set C.GL_n_k :=
  { g | (∀ i, g.val i i = 1) ∧ (∀ i j, j < i → g.val i j = 0) }

/-- *Lower unipotent subgroup of $GL_n(k)$*: matrices with $1$'s on the diagonal and zeros
strictly above the diagonal. -/
def LowerUnipotent : Set C.GL_n_k :=
  { g | (∀ i, g.val i i = 1) ∧ (∀ i j, i < j → g.val i j = 0) }

/-- *Diagonal subgroup of $GL_n(k)$*: invertible matrices whose off-diagonal entries vanish. -/
def DiagonalMatrices : Set C.GL_n_k :=
  { g | ∀ i j, i ≠ j → g.val i j = 0 }

/-- *Iwahori subgroup of $GL_n(k)$*: invertible matrices whose diagonal entries are units in
$\mathfrak{o}$, whose strictly-upper-triangular entries lie in $\mathfrak{o}$, and whose
strictly-lower-triangular entries lie in the maximal ideal $\mathfrak{m}$. -/
def IwahoriSubgroupGLn : Set C.GL_n_k :=
  { g |

    (∀ i : Fin C.n, C.isUnitInO (g.val i i)) ∧

    (∀ i j : Fin C.n, i < j → C.isInO (g.val i j)) ∧

    (∀ i j : Fin C.n, j < i → C.isInMaxIdeal (g.val i j)) }

/-- *Maximal compact subgroup $GL_n(\mathfrak{o})$*: invertible matrices over $\mathfrak{o}$
whose inverse also has entries in $\mathfrak{o}$. Equivalently, $GL_n(\mathfrak{o})$ is the
group of $\mathfrak{o}$-linear automorphisms of the standard lattice. -/
def GL_n_o : Set C.GL_n_k :=
  { g |
    (∀ i j : Fin C.n, C.isInO (g.val i j)) ∧
    (∀ i j : Fin C.n, C.isInO (g⁻¹.val i j)) }


end DVRContext
