/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
open Finset BigOperators


namespace AlgebraicTopologyI

noncomputable section

/-- The standard $n$-simplex is contractible: it is a convex subset of $\mathbf{R}^{n+1}$ and
hence has the homotopy type of a point (used to verify acyclicity of star-shaped chain complexes,
Proposition 5.13). -/
instance stdSimplex_contractible (n : ℕ) :
    ContractibleSpace ↥(stdSimplex ℝ (Fin (n + 1))) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩

end
end AlgebraicTopologyI
