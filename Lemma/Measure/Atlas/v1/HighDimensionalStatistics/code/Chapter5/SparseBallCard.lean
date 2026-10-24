import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.SparseBallCard
open Finset Real SparseVarshamovGilbert


namespace SparseVarshamovGilbert

/--
[boolSupport_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean)
-/
@[path]
lemma boolSupport_card
  {d k : ℕ}
  {x : SparseVec d k} :
-- imply
  (boolSupport x.val).card = k :=
-- proof
  x.property

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[compl_boolSupport_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean)
-/
@[path]
lemma compl_boolSupport_card
  {d k : ℕ}
  {x : SparseVec d k}
-- given
  (hkd : k ≤ d) :
-- imply
  (Finset.univ \ boolSupport x.val).card = d - k := by
-- proof
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (boolSupport x.val))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [boolSupport_card] at h; omega

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[disjoint_of_support_subsets](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean)
-/
@[path]
lemma disjoint_of_support_subsets
  {d : ℕ}
  {x : Fin d → Bool}
  {J K : Finset (Fin d)}
-- given
  (hJ : J ⊆ boolSupport x)
  (hK : K ⊆ Finset.univ \ boolSupport x) :
-- imply
  Disjoint J K :=
-- proof
  Finset.disjoint_of_subset_left hJ
    (Finset.disjoint_of_subset_right hK disjoint_sdiff_self_right)

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[boolSupport_flipVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean)
-/
@[path]
lemma boolSupport_flipVec
  {d : ℕ}
  {x : Fin d → Bool}
  {J K : Finset (Fin d)}
-- given
  (hDisj : Disjoint J K) :
-- imply
  boolSupport (flipVec x J K) = (boolSupport x \ J) ∪ K := by
-- proof
  ext i
  simp only [boolSupport, Finset.mem_filter, Finset.mem_univ, true_and, flipVec,
    Finset.mem_union, Finset.mem_sdiff]
  split_ifs with h1 h2
  · constructor
    · simp
    · exact fun h => h.elim (fun ⟨_, a⟩ => absurd h1 a)
      (fun hk => absurd hk (Finset.disjoint_left.mp hDisj h1))
  · exact ⟨fun _ => Or.inr h2, fun _ => rfl⟩
  · exact ⟨fun hxt => Or.inl ⟨hxt, h1⟩, fun h => h.elim (·.1) (absurd · h2)⟩

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[flipVec_preserves_l0norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean)
-/
@[path]
lemma flipVec_preserves_l0norm
  {d : ℕ}
  {x : Fin d → Bool}
  {J K : Finset (Fin d)}
-- given
  (hJ : J ⊆ boolSupport x)
  (hK : K ⊆ Finset.univ \ boolSupport x)
  (hJK : J.card = K.card) :
-- imply
  l0norm (flipVec x J K) = l0norm x := by
-- proof
  unfold l0norm
  show (boolSupport (flipVec x J K)).card = (boolSupport x).card
  rw [boolSupport_flipVec x J K (disjoint_of_support_subsets hJ hK)]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.sdiff_subset
    (Finset.disjoint_of_subset_right hK disjoint_sdiff_self_right))]
  have := Finset.card_sdiff_add_card_eq_card hJ; omega

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[disagree_eq_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean)
-/
@[path]
lemma disagree_eq_union
  {d : ℕ}
  {x : Fin d → Bool}
  {J K : Finset (Fin d)}
-- given
  (hJ : J ⊆ boolSupport x)
  (hK : K ⊆ Finset.univ \ boolSupport x) :
-- imply
  (Finset.univ.filter fun i => x i ≠ flipVec x J K i) = J ∪ K := by
-- proof
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, flipVec, Finset.mem_union]
  split_ifs with h1 h2
  ·
    have hxi : x i = true := by
      have := hJ h1; simp only [boolSupport, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    simp [hxi, h1]
  ·
    have hxi : x i = false := by
      have h := hK h2
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, boolSupport,
        Finset.mem_filter] at h
      exact Bool.eq_false_iff.mpr h
    simp [hxi, h1, h2]
  · simp [h1, h2]

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[hammingDist_of_flipVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean)
-/
@[path]
lemma hammingDist_of_flipVec
  {d : ℕ}
  {x : Fin d → Bool}
  {J K : Finset (Fin d)}
-- given
  (hJ : J ⊆ boolSupport x)
  (hK : K ⊆ Finset.univ \ boolSupport x)
  (hDisj : Disjoint J K) :
-- imply
  hammingDist x (flipVec x J K) = J.card + K.card := by
-- proof
  unfold hammingDist
  rw [disagree_eq_union x J K hJ hK, Finset.card_union_of_disjoint hDisj]

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[flipVec_reconstructs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean)
-/
@[path]
lemma flipVec_reconstructs
  {d : ℕ}
  {x y : Fin d → Bool} :
-- imply
  flipVec x (boolSupport x \ boolSupport y) (boolSupport y \ boolSupport x) = y := by
-- proof
  ext i
  simp only [flipVec, boolSupport, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hxi : x i = true <;> by_cases hyi : y i = true <;> simp [hxi, hyi]

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[sdiff_boolSupport_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean)
-/
@[path]
lemma sdiff_boolSupport_card_eq
  {d k : ℕ}
  {x y : Fin d → Bool}
-- given
  (hx : l0norm x = k)
  (hy : l0norm y = k) :
-- imply
  (boolSupport x \ boolSupport y).card = (boolSupport y \ boolSupport x).card :=
-- proof
  Finset.card_sdiff_eq_card_sdiff_iff.mpr (by unfold boolSupport l0norm at *; omega)

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[hammingDist_eq_two_mul_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean)
-/
@[path]
lemma hammingDist_eq_two_mul_sdiff
  {d k : ℕ}
  {x y : Fin d → Bool}
-- given
  (hx : l0norm x = k)
  (hy : l0norm y = k) :
-- imply
  hammingDist x y = 2 * (boolSupport x \ boolSupport y).card := by
-- proof
  unfold hammingDist
  have hdis : (Finset.univ.filter fun i => x i ≠ y i) =
    (boolSupport x \ boolSupport y) ∪ (boolSupport y \ boolSupport x) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff,
      boolSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    cases (x i) <;> cases (y i) <;> simp
  rw [hdis, Finset.card_union_of_disjoint disjoint_sdiff_sdiff,
    sdiff_boolSupport_card_eq x y hx hy]
  omega
end SparseVarshamovGilbert



-- created on 2026-10-23
