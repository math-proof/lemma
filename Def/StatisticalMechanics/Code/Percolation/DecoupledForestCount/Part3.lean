/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Theorem.StatisticalMechanics.Code.Percolation.DecoupledForestCount.Part2


namespace StatMech.Percolation

open Set SimpleGraph Finset

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


def dfc_CanonBoxOpenForestSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vset : Finset (Site d)) (_ : Nonempty (↑Vset : Type)) (F : SimpleGraph (↑Vset : Type))
    (_ : DecidableRel F.Adj) (vx : Site d → (↑Vset : Type)) (b : Site d → Fin 3 → (↑Vset : Type)),
    (∀ u v, F.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d)) ∧
    F.IsAcyclic ∧
    (∀ v : (↑Vset : Type), 1 ≤ F.degree v) ∧
    (∀ x, x ∈ box d n → IsCanonicalTrifurcation d ω x →
      ((vx x : Site d) = x ∧
       (∀ i, F.Reachable (vx x) (b x i) ∧ b x i ≠ vx x) ∧
       (¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d)))) ∧
    (∀ v : (↑Vset : Type), F.degree v = 1 → (v : Site d) ∈ vertexBoundary d (n + 1))

end StatMech.Percolation
