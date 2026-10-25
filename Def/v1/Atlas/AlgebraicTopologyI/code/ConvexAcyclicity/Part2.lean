/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.ConvexAcyclicity
open Finset BigOperators


namespace AlgebraicTopologyI

noncomputable section

/-- The cone (as a continuous map) on a singular $(n+1)$-simplex `σ` with apex `b` in a single
standard simplex; bundles `coneRawSimplex` with its continuity proof. -/
noncomputable def coneSimplex₁ (m n : ℕ) (b : ↥(stdSimplex ℝ (Fin m)))
    (σ : C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin m)))) :
    C(↥(stdSimplex ℝ (Fin (n + 2))), ↥(stdSimplex ℝ (Fin m))) :=
  ⟨coneRawSimplex m n b σ, coneSimplex_continuous m n b σ⟩

/-- Cone construction on a singular $n$-simplex valued in the product of two standard simplices
$\Delta^p \times \Delta^q$, with apex the pair of base vertices; this produces an $(n+1)$-simplex
used to witness acyclicity of the product chain complex. -/
noncomputable def coneSimplex (p q n : ℕ)
    (σ : SingularSimplex n
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))) :
    SingularSimplex (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) :=
  let b₁ : ↥(stdSimplex ℝ (Fin (p+1))) := ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  let b₂ : ↥(stdSimplex ℝ (Fin (q+1))) := ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  let σ₁ : C(↥(stdSimplex ℝ (Fin (n+1))), ↥(stdSimplex ℝ (Fin (p+1)))) :=
    ContinuousMap.fst.comp σ
  let σ₂ : C(↥(stdSimplex ℝ (Fin (n+1))), ↥(stdSimplex ℝ (Fin (q+1)))) :=
    ContinuousMap.snd.comp σ
  (coneSimplex₁ (p+1) n b₁ σ₁).prodMk (coneSimplex₁ (q+1) n b₂ σ₂)

/-- The chain-level cone operator $h: S_n(\Delta^p \times \Delta^q) \to S_{n+1}(\Delta^p \times
\Delta^q)$ obtained by extending `coneSimplex` linearly; it serves as the chain homotopy from the
identity to the augmentation map. -/
noncomputable def coneChain (p q n : ℕ) :
    SingularChains n (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) →+
    SingularChains (n + 1) (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) :=
  FreeAbelianGroup.map (coneSimplex p q n)


end
end AlgebraicTopologyI
