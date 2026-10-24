import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.TriangleIntersecting
open Finset TriangleIntersecting


namespace TriangleIntersecting

/--
[cliqueFree_three_of_card_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/TriangleIntersecting.lean)
-/
@[path]
lemma cliqueFree_three_of_card_le_two
  {n : ℕ}
  {G : SimpleGraph (Fin n)}
-- given
  (hn : n ≤ 2) :
-- imply
  G.CliqueFree 3 := by
-- proof
  intro s hs
  have hle := Finset.card_le_univ s
  simp only [Fintype.card_fin] at hle
  linarith [hs.card_eq]

end TriangleIntersecting

namespace TriangleIntersecting

/--
[triangle_intersecting_bound_small](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/TriangleIntersecting.lean)
-/
@[path]
lemma triangle_intersecting_bound_small
  {n : ℕ}
  {F : Finset (SimpleGraph (Fin n))}
-- given
  (hn : n ≤ 2)
  (hF : IsTriangleIntersecting F) :
-- imply
  F.card < 2 ^ (Nat.choose n 2 - 2) := by
-- proof
  suffices F.card = 0 by simp [this]
  rw [Finset.card_eq_zero]
  by_contra hne
  have hne' : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨G, hG⟩ := hne'
  have h := hF G hG G hG
  simp only [inf_idem] at h
  exact h (cliqueFree_three_of_card_le_two hn G)

end TriangleIntersecting

namespace TriangleIntersecting

/--
[complete_of_not_cliqueFree_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/TriangleIntersecting.lean)
-/
@[path]
lemma complete_of_not_cliqueFree_fin3
  {G : SimpleGraph (Fin 3)}
-- given
  (h : ¬ G.CliqueFree 3) :
-- imply
  G = ⊤ := by
-- proof
  rw [SimpleGraph.not_cliqueFree_iff] at h
  obtain ⟨f⟩ := h
  have hsurj : Function.Surjective f := Finite.surjective_of_injective f.injective
  ext a b
  simp only [SimpleGraph.top_adj]
  constructor
  · exact G.ne_of_adj
  · intro hne
    obtain ⟨a', ha'⟩ := hsurj a
    obtain ⟨b', hb'⟩ := hsurj b
    have hab' : a' ≠ b' := fun heq => hne (by rw [← ha', ← hb', heq])
    rw [← ha', ← hb']
    rw [f.map_rel_iff]
    simp [SimpleGraph.completeGraph, hab']

end TriangleIntersecting

namespace TriangleIntersecting

/--
[triangle_intersecting_bound_three](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/TriangleIntersecting.lean)
-/
@[path]
lemma triangle_intersecting_bound_three
  {F : Finset (SimpleGraph (Fin 3))}
-- given
  (hF : IsTriangleIntersecting F) :
-- imply
  F.card < 2 ^ (Nat.choose 3 2 - 2) := by
-- proof
  norm_num
  suffices h : F ⊆ ({⊤} : Finset (SimpleGraph (Fin 3))) by
    have := Finset.card_le_card h
    simp at this
    omega
  intro G hG
  simp only [Finset.mem_singleton]
  exact complete_of_not_cliqueFree_fin3 G (by have := hF G hG G hG; simpa using this)

end TriangleIntersecting

namespace TriangleIntersecting

/--
[coverage_arithmetic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/TriangleIntersecting.lean)
-/
@[path]
lemma coverage_arithmetic
  {r s m k : ℕ}
-- given
  (hr : 1 ≤ r)
  (hcov : k * m = r * s)
  (hlt : 2 * r < m)
  (hk : 0 < k) :
-- imply
  (r - 1) * s < (m - 2) * k := by
-- proof
  have hm : 2 ≤ m := by omega
  zify [hr, hm] at *
  nlinarith

end TriangleIntersecting

namespace TriangleIntersecting

/--
[bound_from_pow_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/TriangleIntersecting.lean)
-/
@[path]
lemma bound_from_pow_bound
  {F_card r s m k : ℕ}
-- given
  (hpow : F_card ^ k ≤ (2 ^ (r - 1)) ^ s)
  (harith : (r - 1) * s < (m - 2) * k) :
-- imply
  F_card < 2 ^ (m - 2) := by
-- proof
  have h1 : (2 ^ (r - 1)) ^ s < (2 ^ (m - 2)) ^ k := by
    rw [← pow_mul, ← pow_mul]
    exact Nat.pow_lt_pow_right (by omega) harith
  exact lt_of_pow_lt_pow_left' k (lt_of_le_of_lt hpow h1)
/-- Existence of a Shearer-style bipartition covering for any non-empty triangle-intersecting
family on $n \ge 4$ vertices, providing parameters $r,s,k$ along with the projection bound
$|F|^k \le (2^{r-1})^s$ used to derive the main theorem. -/

end TriangleIntersecting


-- created on 2026-10-23
