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
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section32
open Set Function


namespace OrientationTheorem

variable {M : Type*} [TopologicalSpace M]

/-- Build a `MayerVietorisLadder` from the full Mayer–Vietoris long exact
sequences in `Hrel` and `Γsec` together with the commutation hypotheses.
Uses the vanishing part of the orientation theorem on `A ∩ B` to derive
injectivity of `mvα` and of the higher-degree maps `mvα_q` for `q > n`,
since their kernels lie in `Hrel (q+1) (A ∩ B) = 0`. -/
def MayerVietorisLadder.ofExactSequences
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (A B : Set M) (_hA : IsClosed A) (_hB : IsClosed B)
    (_hOT_AB : OrientationTheoremResult n Hrel Γsec jMap (A ∩ B))

    (mvα_q : ∀ q, Hrel q (A ∪ B) →+ Hrel q A × Hrel q B)
    (mvβ_q : ∀ q, Hrel q A × Hrel q B →+ Hrel q (A ∩ B))
    (mvδ_q : ∀ q, Hrel (q + 1) (A ∩ B) →+ Hrel q (A ∪ B))

    (mv_exact_δα : ∀ q, Exact (mvδ_q q) (mvα_q q))
    (mv_exact_αβ : ∀ q, Exact (mvα_q q) (mvβ_q q))

    (secα : Γsec (A ∪ B) →+ Γsec A × Γsec B)
    (secβ : Γsec A × Γsec B →+ Γsec (A ∩ B))
    (sec_inj : ∀ x, secα x = 0 → x = 0)
    (sec_exact : Exact secα secβ)

    (comm_α : secα.comp (jMap (A ∪ B)) =
      (AddMonoidHom.prodMap (jMap A) (jMap B)).comp (mvα_q n))
    (comm_β : secβ.comp (AddMonoidHom.prodMap (jMap A) (jMap B)) =
      (jMap (A ∩ B)).comp (mvβ_q n)) :
    MayerVietorisLadder n Hrel Γsec jMap A B where
  mvα := mvα_q n
  mvβ := mvβ_q n
  secα := secα
  secβ := secβ
  mv_inj := by


    intro x hx

    obtain ⟨y, rfl⟩ := (mv_exact_δα n x).mp hx

    have hy : y = 0 := _hOT_AB.vanishing (n + 1) (by omega) y
    rw [hy, map_zero]
  mv_exact := mv_exact_αβ n
  sec_inj := sec_inj
  sec_exact := sec_exact
  comm_α := comm_α
  comm_β := comm_β
  mv_inj_q := by
    intro q hq
    exact ⟨mvα_q q, by
      intro x hx
      obtain ⟨y, rfl⟩ := (mv_exact_δα q x).mp hx

      have hy : y = 0 := _hOT_AB.vanishing (q + 1) (by omega) y
      rw [hy, map_zero]⟩

end OrientationTheorem
