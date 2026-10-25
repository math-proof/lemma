/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Class.v1.Atlas.Buildings.code.Valuation.IwahoriDecomp
open Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]


section GL2

variable {C}

/-- *Construct an invertible $2\times 2$ matrix from a function*: given a $2\times 2$ matrix
$f$ over the fraction field $k$ with nonzero determinant, produce the corresponding element
of $GL_2(k)$. The construction uses `unitOfDetInvertible` together with `invertibleOfNonzero`
to convert nonvanishing of the determinant into invertibility data. -/
noncomputable def mkGL2 (f : Fin 2 → Fin 2 → C.k)
    (hdet : (show Matrix (Fin 2) (Fin 2) C.k from f).det ≠ 0) :
    GL (Fin 2) C.k := by
  haveI : Invertible (show Matrix (Fin 2) (Fin 2) C.k from f).det :=
    invertibleOfNonzero hdet
  exact unitOfDetInvertible (show Matrix (Fin 2) (Fin 2) C.k from f)


/-- *The Iwahori subgroup of $GL_2$*: elements of $GL_2(k)$ whose diagonal entries are units
in $\mathfrak{o}$, whose upper-right entry lies in $\mathfrak{o}$, and whose lower-left entry
lies in the maximal ideal $\mathfrak{m}$. -/
def IwahoriGL2 : Set (GL (Fin 2) C.k) :=
  { g |
    C.isUnitInO (g.val 0 0) ∧ C.isUnitInO (g.val 1 1) ∧
    C.isInO (g.val 0 1) ∧ C.isInMaxIdeal (g.val 1 0) }

/-- *Upper unipotent subgroup of $GL_2$*: invertible matrices of the form
$\begin{pmatrix} 1 & * \\ 0 & 1 \end{pmatrix}$. -/
def UpperUnipGL2 : Set (GL (Fin 2) C.k) :=
  { g | g.val 0 0 = 1 ∧ g.val 1 1 = 1 ∧ g.val 1 0 = 0 }

/-- *Lower unipotent subgroup of $GL_2$*: invertible matrices of the form
$\begin{pmatrix} 1 & 0 \\ * & 1 \end{pmatrix}$. -/
def LowerUnipGL2 : Set (GL (Fin 2) C.k) :=
  { g | g.val 0 0 = 1 ∧ g.val 1 1 = 1 ∧ g.val 0 1 = 0 }

/-- *Diagonal subgroup of $GL_2$*: invertible matrices of the form
$\begin{pmatrix} * & 0 \\ 0 & * \end{pmatrix}$. -/
def DiagGL2 : Set (GL (Fin 2) C.k) :=
  { g | g.val 0 1 = 0 ∧ g.val 1 0 = 0 }


/-- *Generic-indexed formulation of the Iwahori subgroup*: an element $g \in GL_2(k)$ belongs
to the Iwahori subgroup iff its diagonal entries are units, its strictly-upper-triangular
entries lie in $\mathfrak{o}$, and its strictly-lower-triangular entries lie in $\mathfrak{m}$.
This form quantifies over indices and is convenient for later generalisations. -/
def IwahoriGL2Gen : Set (GL (Fin 2) C.k) :=
  { g |
    (∀ i : Fin 2, C.isUnitInO (g.val i i)) ∧
    (∀ i j : Fin 2, i < j → C.isInO (g.val i j)) ∧
    (∀ i j : Fin 2, j < i → C.isInMaxIdeal (g.val i j)) }

/-- *Generic-indexed formulation of the lower unipotent subgroup*: an element $g \in GL_2(k)$
is lower unipotent iff its diagonal entries are $1$ and its strictly-upper-triangular entries
vanish. -/
def LowerUnipGL2Gen : Set (GL (Fin 2) C.k) :=
  { g |
    (∀ i : Fin 2, g.val i i = 1) ∧
    (∀ i j : Fin 2, i < j → g.val i j = 0) }

/-- *Generic-indexed formulation of the upper unipotent subgroup*: an element $g \in GL_2(k)$
is upper unipotent iff its diagonal entries are $1$ and its strictly-lower-triangular entries
vanish. -/
def UpperUnipGL2Gen : Set (GL (Fin 2) C.k) :=
  { g |
    (∀ i : Fin 2, g.val i i = 1) ∧
    (∀ i j : Fin 2, j < i → g.val i j = 0) }

/-- *Generic-indexed formulation of the diagonal subgroup*: an element $g \in GL_2(k)$ is
diagonal iff all its off-diagonal entries vanish. -/
def DiagGL2Gen : Set (GL (Fin 2) C.k) :=
  { g | ∀ i j : Fin 2, i ≠ j → g.val i j = 0 }

end GL2
end DVRContext
