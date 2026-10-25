/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PontrjaginObstructions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic
import Structure.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part3
set_option autoImplicit false
open scoped Manifold


/-- Hirzebruch signature theorem (axiomatized): $p_1 \cdot [M] = 3 \sigma(M)$ for closed
oriented $4$-manifolds. -/
def ClosedOriented4ManifoldData.ofChernPontrjagin
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M]
    (hcp : HasChernPontrjaginData M) :
    ClosedOriented4ManifoldData M where
  p₁ := hcp.p₁
  b₂_plus := htop.Q.b₂_plus
  b₂_minus := htop.Q.b₂_minus
  signature := htop.Q.signature
  signature_eq := htop.Q.signature_eq
  intersectionForm := fun x y =>
    htop.Q.bilinForm
      (fun i => x (Fin.cast htop.Q.rank_decomp i))
      (fun i => y (Fin.cast htop.Q.rank_decomp i))
  intersectionForm_symm := fun _ _ => htop.Q.bilinForm_symm _ _


