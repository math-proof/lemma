/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.IwahoriGLnHelpers
import Lemma.Fin.ValElimMatrix.eq.Transvection.of.Ne
import Theorem.v1.Atlas.Buildings.code.Building.DiagBlockEmbed
set_option maxHeartbeats 400000

open Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section DiagBlockEmbed

variable {n : ℕ}

/-- The block-diagonal matrix $\mathrm{diag}(a, A)$ of size $(n+1) \times
(n+1)$, putting the scalar $a$ in the top-left corner and the matrix $A$ in
the bottom-right block. -/
noncomputable def diagBlockEmbedMatrix (a : C.k) (A : Matrix (Fin n) (Fin n) C.k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) C.k :=
  (reindexAlgEquiv C.k C.k (finBlockEquiv n))
    (fromBlocks (scalarMat1 C a) 0 0 A)

/-- The diagonal block embedding $\mathrm{GL}_n(k) \hookrightarrow
\mathrm{GL}_{n+1}(k)$ sending $M$ to $\mathrm{diag}(a, M)$, with $a \in
k^\times$ in the leading slot. -/
noncomputable def diagBlockEmbedGL (a : C.kˣ) (M : GL (Fin n) C.k) : GL (Fin (n + 1)) C.k := by
  refine ⟨
    diagBlockEmbedMatrix C a.val M.val,
    diagBlockEmbedMatrix C (a.val)⁻¹ M.inv,
    ?_, ?_⟩
  ·
    simp only [diagBlockEmbedMatrix]
    rw [← reindexAlgEquiv_mul, fromBlocks_multiply]
    have hscal : scalarMat1 C a.val * scalarMat1 C (a.val)⁻¹ = 1 := by
      ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
    simp [hscal, fromBlocks_one]
  ·
    simp only [diagBlockEmbedMatrix]
    rw [← reindexAlgEquiv_mul, fromBlocks_multiply]
    have hscal : scalarMat1 C (a.val)⁻¹ * scalarMat1 C a.val = 1 := by
      ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
    simp [hscal, fromBlocks_one]

end DiagBlockEmbed
end DVRContext
