/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.IwahoriGLnDefs
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Reindex

set_option maxHeartbeats 200000

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section ElimMatrix

variable {n : ℕ}

/-- The transvection / elementary matrix $E_{ij}(c) = 1 + c \cdot e_{ij}$ packaged as an element of
$\mathrm{GL}_n(k)$, with explicit two-sided inverse $E_{ij}(-c)$. -/
noncomputable def elimMatrix (i j : Fin n) (hij : i ≠ j) (c : C.k) :
    GL (Fin n) C.k :=
  ⟨transvection i j c, transvection i j (-c),
    by simp [transvection, Matrix.add_mul, Matrix.mul_add, hij.symm, add_assoc, ← single_add],
    by simp [transvection, Matrix.add_mul, Matrix.mul_add, hij.symm, add_assoc, ← single_add]⟩

/-- Equivalence $\mathrm{Fin}\,1 \oplus \mathrm{Fin}\,n \simeq \mathrm{Fin}(n + 1)$ obtained by
composing `finSumFinEquiv` with the natural cast $\mathrm{Fin}(1 + n) \simeq \mathrm{Fin}(n + 1)$. -/
noncomputable def finBlockEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (Fin.castOrderIso (by omega)).toEquiv

/-- Block embedding $\mathrm{GL}_n \hookrightarrow \mathrm{GL}_{n+1}$ at the matrix level: place the
$n \times n$ matrix $A$ in the lower-right corner of the $(n+1) \times (n+1)$ matrix and put a
single $1$ in the upper-left corner. -/
noncomputable def blockEmbedMatrix (A : Matrix (Fin n) (Fin n) C.k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) C.k :=
  (reindexAlgEquiv C.k C.k (finBlockEquiv n))
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) C.k) 0 0 A)

/-- Block embedding $\mathrm{GL}_n(k) \hookrightarrow \mathrm{GL}_{n+1}(k)$ at the group level:
upgrade `blockEmbedMatrix` to a unit by carrying the explicit inverse along. -/
noncomputable def blockEmbedGL (g : GL (Fin n) C.k) : GL (Fin (n + 1)) C.k := by
  refine ⟨blockEmbedMatrix C g.val, blockEmbedMatrix C g.inv, ?_, ?_⟩
  · simp only [blockEmbedMatrix]
    rw [← reindexAlgEquiv_mul, fromBlocks_multiply]
    simp [fromBlocks_one]
  · simp only [blockEmbedMatrix]
    rw [← reindexAlgEquiv_mul, fromBlocks_multiply]
    simp [fromBlocks_one]
