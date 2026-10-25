/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section30.Part4
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section30
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.Algebra.FiveLemma
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Def.v1.Atlas.AlgebraicTopologyI.code.Section32
open Set Function


namespace OrientationTheorem

variable {M : Type*} [TopologicalSpace M]

/-- Abstract data of the relative Mayer–Vietoris long exact sequences in
all degrees together with the section-sequence and compatibility
conditions, packaged so that `MayerVietorisLadder.ofExactSequences` can
be invoked from a single bundle. -/
structure RelativeMVSequenceData
    {M : Type*} [TopologicalSpace M]
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (A B : Set M) where
  mvα_q : ∀ q, Hrel q (A ∪ B) →+ Hrel q A × Hrel q B
  mvβ_q : ∀ q, Hrel q A × Hrel q B →+ Hrel q (A ∩ B)
  mvδ_q : ∀ q, Hrel (q + 1) (A ∩ B) →+ Hrel q (A ∪ B)
  mv_exact_δα : ∀ q, Exact (mvδ_q q) (mvα_q q)
  mv_exact_αβ : ∀ q, Exact (mvα_q q) (mvβ_q q)
  secα : Γsec (A ∪ B) →+ Γsec A × Γsec B
  secβ : Γsec A × Γsec B →+ Γsec (A ∩ B)
  sec_inj : ∀ x, secα x = 0 → x = 0
  sec_exact : Exact secα secβ
  comm_α : secα.comp (jMap (A ∪ B)) =
    (AddMonoidHom.prodMap (jMap A) (jMap B)).comp (mvα_q n)
  comm_β : secβ.comp (AddMonoidHom.prodMap (jMap A) (jMap B)) =
    (jMap (A ∩ B)).comp (mvβ_q n)

/-- Abstract data witnessing that `G (⋂ j, A j)` is the colimit of the
sequence `G (A i)` along the inclusions `A (i+1) ⊆ A i`: restriction
maps `ρ i` to the intersection, transition maps `φ i j` compatible with
them, and the two filtered-colimit conditions (every element of the
limit comes from some `G (A i)`, and an element vanishing in the limit
already vanishes at some larger stage). -/
structure RelativeHomologyColimitData {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X)
    (G : Set X → Type*)
    [∀ K, AddCommGroup (G K)] where
  ρ : ∀ i, G (A i) →+ G (⋂ j, A j)
  φ : ∀ (i j : ℕ), i ≤ j → G (A i) →+ G (A j)
  compat : ∀ i j (hij : i ≤ j), (ρ j).comp (φ i j hij) = ρ i
  surj : ∀ (x : G (⋂ j, A j)), ∃ i, ∃ g : G (A i), ρ i g = x
  inj : ∀ i (g : G (A i)), ρ i g = 0 → ∃ j, ∃ hij : i ≤ j, φ i j hij g = 0

/-- Bundle of all colimit data needed for the `orientation_theorem_iInter`
proof at a single decreasing compact sequence: per-degree
`RelativeHomologyColimitData` for `Hrel q`, one for `Γsec`, and the
compatibility of `jMap` with the restriction and transition maps. -/
structure ColimitDataForDecreasingCompact {M : Type*} [TopologicalSpace M]
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : ℕ → Set M)
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K) where
  colH : ∀ q, RelativeHomologyColimitData A (Hrel q)
  colΓ : RelativeHomologyColimitData A Γsec
  hjMap_ρ : ∀ i, (colΓ.ρ i).comp (jMap (A i)) = (jMap (⋂ j, A j)).comp ((colH n).ρ i)
  hjMap_φ : ∀ i j (hij : i ≤ j),
    (colΓ.φ i j hij).comp (jMap (A i)) = (jMap (A j)).comp ((colH n).φ i j hij)

end OrientationTheorem
