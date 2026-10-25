import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.InvariantPreserve
open Finset Finsupp MulAction Function InvariantPreserve
open scoped Classical Pointwise


namespace InvariantPreserve

/--
[raisingOp_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma raisingOp_single
  {n : ℕ}
  {S : Finset (Fin n)}
  {r : ℝ} :
-- imply
  raisingOp n (Finsupp.single S r) = r • raisingOnBasis n S := by
-- proof
  simp only [raisingOp, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
variable (G : Type*) [Group G] [MulAction G (Fin n)]
attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction
  Finsupp.comapDistribMulAction

end InvariantPreserve

namespace InvariantPreserve

/--
[comapSMul_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma comapSMul_zero
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {g : G} :
-- imply
  (g • (0 : Finset (Fin n) →₀ ℝ)) = 0 :=
-- proof
  Finsupp.mapDomain_zero

end InvariantPreserve

namespace InvariantPreserve

/--
[comapSMul_eq_mapDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma comapSMul_eq_mapDomain
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {g : G}
  {v : Finset (Fin n) →₀ ℝ} :
-- imply
  g • v = Finsupp.mapDomain (g • ·) v :=
-- proof
  rfl

end InvariantPreserve

namespace InvariantPreserve

/--
[comapSMul_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma comapSMul_add
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {g : G}
  {v w : Finset (Fin n) →₀ ℝ} :
-- imply
  g • (v + w) = g • v + g • w := by
-- proof
  simp only [comapSMul_eq_mapDomain, Finsupp.mapDomain_add]

end InvariantPreserve

namespace InvariantPreserve

/--
[smul_ssubset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma smul_ssubset
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {g : G}
  {S T : Finset (Fin n)}
-- given
  (h : S ⊂ T) :
-- imply
  g • S ⊂ g • T :=
-- proof
  (Finset.image_ssubset_image (MulAction.injective g)).mpr h

end InvariantPreserve

namespace InvariantPreserve

/--
[smul_upperCovers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma smul_upperCovers
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {g : G}
  {S : Finset (Fin n)} :
-- imply
  (upperCovers n S).image (g • ·) = upperCovers n (g • S) := by
-- proof
  ext T
  simp only [upperCovers, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨T', ⟨hss, hcard⟩, rfl⟩
    exact ⟨smul_ssubset n G g S T' hss,
      by rw [Finset.card_smul_finset, hcard, Finset.card_smul_finset]⟩
  · intro ⟨hss, hcard⟩
    refine ⟨g⁻¹ • T, ⟨?_, ?_⟩, by rw [smul_inv_smul]⟩
    · rw [← inv_smul_smul g S]
      exact smul_ssubset n G g⁻¹ (g • S) T hss
    · rw [Finset.card_smul_finset, hcard, Finset.card_smul_finset]

end InvariantPreserve

namespace InvariantPreserve

/--
[smul_raisingOnBasis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma smul_raisingOnBasis
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {g : G}
  {S : Finset (Fin n)} :
-- imply
  Finsupp.mapDomain (g • ·) (raisingOnBasis n S) = raisingOnBasis n (g • S) := by
-- proof
  simp only [raisingOnBasis, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single]
  rw [← smul_upperCovers n G g S]
  rw [Finset.sum_image]
  intro T₁ _ T₂ _ h
  exact MulAction.injective g h

end InvariantPreserve

namespace InvariantPreserve

/--
[raisingOp_comm_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma raisingOp_comm_smul
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {g : G}
  {v : Finset (Fin n) →₀ ℝ} :
-- imply
  g • raisingOp n v = raisingOp n (g • v) := by
-- proof
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero, comapSMul_zero]
  | add f₁ f₂ hf₁ hf₂ =>
    simp only [map_add, comapSMul_add, hf₁, hf₂]
  | single S r =>
    simp only [raisingOp_single, comapSMul_eq_mapDomain, Finsupp.mapDomain_smul,
      Finsupp.mapDomain_single, smul_raisingOnBasis]

end InvariantPreserve

namespace InvariantPreserve

/--
[linearMap_preserves_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma linearMap_preserves_invariant
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {f : (Finset (Fin n) →₀ ℝ) →ₗ[ℝ] (Finset (Fin n) →₀ ℝ)}
  {v : Finset (Fin n) →₀ ℝ}
-- given
  (hcomm : ∀ g : G, ∀ v : Finset (Fin n) →₀ ℝ, g • f v = f (g • v))
  (hv : v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n))) :
-- imply
  f v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n)) := by
-- proof
  intro g
  rw [hcomm g v]
  congr 1
  exact hv g

end InvariantPreserve

namespace InvariantPreserve

/--
[raisingOp_mem_invariantSubspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma raisingOp_mem_invariantSubspace
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {v : Finset (Fin n) →₀ ℝ}
-- given
  (hv : v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n))) :
-- imply
  raisingOp n v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n)) :=
-- proof
  linearMap_preserves_invariant n G (raisingOp n) (raisingOp_comm_smul n G) hv

end InvariantPreserve

namespace InvariantPreserve

/--
[raisingOnBasis_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma raisingOnBasis_support_subset
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {S : Finset (Fin n)} :
-- imply
  (raisingOnBasis n S).support ⊆ upperCovers n S := by
-- proof
  intro T hT
  have := Finsupp.support_finset_sum (s := upperCovers n S)
    (f := fun T => Finsupp.single T (1 : ℝ)) hT
  rw [Finset.mem_biUnion] at this
  obtain ⟨T', hT'mem, hT'sup⟩ := this
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hT'sup
  exact hT'sup ▸ hT'mem

end InvariantPreserve

namespace InvariantPreserve

/--
[card_of_mem_upperCovers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma card_of_mem_upperCovers
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {S T : Finset (Fin n)}
-- given
  (hT : T ∈ upperCovers n S) :
-- imply
  T.card = S.card + 1 := by
-- proof
  simp only [upperCovers, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  exact hT.2

end InvariantPreserve

namespace InvariantPreserve

/--
[raisingOp_support_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma raisingOp_support_card
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {i : ℕ}
  {v : Finset (Fin n) →₀ ℝ}
-- given
  (hv : ∀ x ∈ v.support, x.card = i) :
-- imply
  ∀ y ∈ (raisingOp n v).support, y.card = i + 1 := by
-- proof
  intro y hy
  have hrw : raisingOp n v = v.sum (fun S r => r • raisingOnBasis n S) := by
    simp only [raisingOp, Finsupp.lsum_apply]
    congr 1
  rw [hrw] at hy
  have hsup := Finsupp.support_sum hy
  rw [Finset.mem_biUnion] at hsup
  obtain ⟨S, hSmem, hySsup⟩ := hsup
  have hySrob : y ∈ (raisingOnBasis n S).support := Finsupp.support_smul hySsup
  have hT_in_uc := raisingOnBasis_support_subset n S hySrob
  have := card_of_mem_upperCovers n hT_in_uc
  rwa [hv S hSmem] at this

end InvariantPreserve

namespace InvariantPreserve

/--
[raisingOp_supportedAtLevel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma raisingOp_supportedAtLevel
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {i : ℕ}
  {v : Finset (Fin n) →₀ ℝ}
-- given
  (hv : supportedAtLevel n i v) :
-- imply
  supportedAtLevel n (i + 1) (raisingOp n v) :=
-- proof
  raisingOp_support_card n i v hv

end InvariantPreserve

namespace InvariantPreserve

/--
[raisingOp_mem_invariantSubspace_graded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean)
-/
@[path]
lemma raisingOp_mem_invariantSubspace_graded
  {n : ℕ}
  {G : Type*}
  [Group G]
  [MulAction G (Fin n)]
  {v : Finset (Fin n) →₀ ℝ}
  {i : ℕ}
-- given
  (hv_inv : v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n)))
  (hv_level : supportedAtLevel n i v) :
-- imply
  raisingOp n v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n)) ∧ supportedAtLevel n (i + 1) (raisingOp n v) :=
-- proof
  ⟨raisingOp_mem_invariantSubspace n G hv_inv, raisingOp_supportedAtLevel n hv_level⟩
end InvariantPreserve



-- created on 2026-10-23
