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
open Set Function


namespace OrientationTheorem

variable {M : Type*} [TopologicalSpace M]

/-- **Conclusion of Theorem 32.1 for a compact subset `K`.** Packages the
two assertions of the orientation theorem for an `n`-manifold `M` and a
compact set `K ⊆ M`: the relative homology groups `Hrel q K` vanish for
`q > n`, and the comparison map `jMap K : Hrel n K → Γsec K` to sections
of the orientation sheaf is a bijection. Stated abstractly so that the
proof structure of Section 32 can be reused for any homology theory
`Hrel`/section functor `Γsec` satisfying the appropriate axioms. -/
structure OrientationTheoremResult
    (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [inst : ∀ q A, AddCommGroup (Hrel q A)]
    (Γsec : Set M → Type*)
    [inst' : ∀ A, AddCommGroup (Γsec A)]
    (jMap : (A : Set M) → Hrel n A →+ Γsec A)
    (K : Set M) : Prop where
  vanishing : ∀ q, q > n → ∀ x : Hrel q K, x = 0
  isomorphism : Bijective (jMap K)

/-- **Mayer–Vietoris ladder data for Proposition 32.2.** Records the
relevant portion of the commutative diagram with exact rows used to prove
that if the orientation theorem holds for `A`, `B`, and `A ∩ B`, then it
holds for `A ∪ B`: the top row is the relative-homology Mayer–Vietoris
sequence at degrees `n` and `q > n`, the bottom row is the
Mayer–Vietoris sequence for sections of the orientation sheaf, and
`jMap` provides the comparison map between them. -/
structure MayerVietorisLadder
    (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (A B : Set M) where
  mvα : Hrel n (A ∪ B) →+ Hrel n A × Hrel n B
  mvβ : Hrel n A × Hrel n B →+ Hrel n (A ∩ B)
  secα : Γsec (A ∪ B) →+ Γsec A × Γsec B
  secβ : Γsec A × Γsec B →+ Γsec (A ∩ B)
  mv_inj : ∀ x, mvα x = 0 → x = 0
  mv_exact : Exact mvα mvβ
  sec_inj : ∀ x, secα x = 0 → x = 0
  sec_exact : Exact secα secβ
  comm_α : secα.comp (jMap (A ∪ B)) =
    (AddMonoidHom.prodMap (jMap A) (jMap B)).comp mvα
  comm_β : secβ.comp (AddMonoidHom.prodMap (jMap A) (jMap B)) =
    (jMap (A ∩ B)).comp mvβ
  mv_inj_q : ∀ q, q > n →
    ∃ (αq : Hrel q (A ∪ B) →+ Hrel q A × Hrel q B),
      ∀ x, αq x = 0 → x = 0

end OrientationTheorem
