/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Theorem.StatisticalMechanics.Code.Percolation.DecoupledForestCount.Part3


namespace StatMech.Percolation

open Set SimpleGraph Finset

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


def dfc_CanonArmForestReachingSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (c : Site d → Fin 3 → Site d) (zr : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d (n + 1)) ∧
    (∃ v, spc_OnBPath T B v) ∧
    (∀ x, x ∈ box d n → IsCanonicalTrifurcation d ω x →
      (∀ i, T.Adj x (c x i)) ∧
      (¬ Connected d (removeSite x ω) (c x 0) (c x 1) ∧
       ¬ Connected d (removeSite x ω) (c x 0) (c x 2) ∧
       ¬ Connected d (removeSite x ω) (c x 1) (c x 2)) ∧
      (∀ i, zr x i ∈ B ∧ ∃ w : T.Walk (c x i) (zr x i), x ∉ w.support))


def dfc_CanonSpanForestArmsSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (m : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d (n + 1)) ∧
    (∃ v, spc_OnBPath T B v) ∧
    (∀ x, x ∈ box d n → IsCanonicalTrifurcation d ω x →
      spc_OnBPath T B x ∧
      ((m x 0 ≠ m x 1 ∧ m x 0 ≠ m x 2 ∧ m x 1 ≠ m x 2) ∧
       (∀ i, T.Adj x (m x i) ∧ spc_OnBPath T B (m x i)) ∧
       (¬ Connected d (removeSite x ω) (m x 0) (m x 1) ∧
        ¬ Connected d (removeSite x ω) (m x 0) (m x 2) ∧
        ¬ Connected d (removeSite x ω) (m x 1) (m x 2))))


end StatMech.Percolation
