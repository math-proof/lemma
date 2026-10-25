import Mathlib
import Def.Analysis.Misc.erdos_613.Part9
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

lemma redBlock1B1_subset_B1Set (color : Sym2 V → Fin 2) :
  redBlock1B1 color ⊆ B1Set := by
  classical
  intro v hv
  rcases Finset.mem_filter.1 hv with ⟨_, hB1⟩
  -- From `isB1 v`, `v = B1 j` for some `j`, hence in the image.
  cases v with
  | B1 j =>
      simp [B1Set]    -- `v` is exactly `B1 j`, hence in the image of `j`.
  | A1 _ => cases hB1
  | A2 _ => cases hB1
  | B2 _ => cases hB1
  | apex => cases hB1

lemma redBlock2B2_subset_B2Set (color : Sym2 V → Fin 2) :
  redBlock2B2 color ⊆ B2Set := by
  classical
  intro v hv
  rcases Finset.mem_filter.1 hv with ⟨_, hB2⟩
  cases v with
  | B2 j =>
      simp [B2Set]
  | A1 _ => cases hB2
  | B1 _ => cases hB2
  | A2 _ => cases hB2
  | apex => cases hB2

lemma card_B1Set_le_5 : (B1Set).card ≤ 5 := by
  classical
  -- image has card ≤ card of the domain
  simpa [B1Set, Fintype.card_fin] using
    (Finset.card_image_le : (Finset.univ.image (fun j : Fin 5 => B1 j)).card ≤ (Finset.univ : Finset (Fin 5)).card)

lemma card_B2Set_le_5 : (B2Set).card ≤ 5 := by
  classical
  simpa [B2Set, Fintype.card_fin] using
    (Finset.card_image_le : (Finset.univ.image (fun j : Fin 5 => B2 j)).card ≤ (Finset.univ : Finset (Fin 5)).card)

lemma redBlock1B1_card_le_5 (color : Sym2 V → Fin 2) :
  (redBlock1B1 color).card ≤ 5 :=
  (Finset.card_le_card (redBlock1B1_subset_B1Set color)).trans card_B1Set_le_5

lemma redBlock2B2_card_le_5 (color : Sym2 V → Fin 2) :
  (redBlock2B2 color).card ≤ 5 :=
  (Finset.card_le_card (redBlock2B2_subset_B2Set color)).trans card_B2Set_le_5

/-! # Existence of a red neighbor in the clique parts {name}`A1` / {name}`A2` -/

/-- If block 1 receives at least 6 red neighbors from {name}`apex`, then one of them lies in {name}`A1`. -/
lemma exists_red_A1_of_block1_ge6
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock1 color).card) :
    ∃ i : Fin 2, G.Adj apex (A1 i) ∧ color (s(apex, A1 i)) = 1 := by
  classical
  -- From the decomposition `|redBlock1| = |A1-part| + |B1-part|`
  -- and `|B1-part| ≤ 5`, we get `|A1-part| ≥ 1`.
  have hdecomp := redBlock1_card_eq_sum color
  have hB1le := redBlock1B1_card_le_5 color
  have hposA1 : 0 < (redBlock1A1 color).card := by
    -- If `A1-part` were empty, then `|redBlock1| = |B1-part| ≤ 5`, contradicting `≥ 6`.
    by_contra hzero
    have hz : (redBlock1A1 color).card = 0 := Nat.eq_zero_of_not_pos hzero
    have : (redBlock1 color).card = (redBlock1B1 color).card := by
      simp [hdecomp, hz, zero_add]
    have : (redBlock1 color).card ≤ 5 := by simpa [this] using hB1le
    grind
  -- Choose a vertex `v` in the `A1` part.
  rcases Finset.card_pos.1 hposA1 with ⟨v, hv⟩
  -- From membership we extract adjacency and redness.
  rcases Finset.mem_filter.1 hv with ⟨hRN, hA1⟩
  rcases Finset.mem_filter.1 hRN with ⟨hNei, hRed⟩
  -- Now `v` must be of the form `A1 i`.
  cases v with
  | A1 i =>
      exact ⟨i, by aesop, by simpa using hRed⟩
  | B1 _ => cases hA1
  | A2 _ => cases hA1
  | B2 _ => cases hA1
  | apex  => cases hA1

/-- If block 2 receives at least 6 red neighbors from {name}`apex`, then one of them lies in {name}`A2`. -/
lemma exists_red_A2_of_block2_ge6
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock2 color).card) :
    ∃ i : Fin 3, G.Adj apex (A2 i) ∧ color (s(apex, A2 i)) = 1 := by
  classical
  have hdecomp := redBlock2_card_eq_sum color
  have hB2le := redBlock2B2_card_le_5 color
  have hposA2 : 0 < (redBlock2A2 color).card := by
    by_contra hzero
    have hz : (redBlock2A2 color).card = 0 := Nat.eq_zero_of_not_pos hzero
    have : (redBlock2 color).card = (redBlock2B2 color).card := by
      simp [hdecomp, hz, zero_add]
    have : (redBlock2 color).card ≤ 5 := by simpa [this] using hB2le
    grind
  rcases Finset.card_pos.1 hposA2 with ⟨v, hv⟩
  rcases Finset.mem_filter.1 hv with ⟨hRN, hA2⟩
  rcases Finset.mem_filter.1 hRN with ⟨hNei, hRed⟩
  cases v with
  | A2 i =>
      exact ⟨i, by aesop, by simpa using hRed⟩
  | A1 _ => cases hA2
  | B1 _ => cases hA2
  | B2 _ => cases hA2
  | apex  => cases hA2

/-- Corollary: under the “no blue star” hypothesis, there is a red neighbor of {name}`apex`
in the appropriate clique {name}`A1` or {name}`A2`. -/
lemma exists_red_clique_neighbor
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    (∃ i : Fin 2, G.Adj apex (A1 i) ∧ color (s(apex, A1 i)) = 1) ∨
    (∃ i : Fin 3, G.Adj apex (A2 i) ∧ color (s(apex, A2 i)) = 1) := by
  classical
  -- Your previous lemma:
  have h := exists_block_receives_at_least_6_red color hNoBlueStar
  rcases h with h1 | h2
  · exact Or.inl (exists_red_A1_of_block1_ge6 color h1)
  · exact Or.inr (exists_red_A2_of_block2_ge6 color h2)

end PikhurkoN5

-- 7. triangle-or-star from the clique vertex

namespace PikhurkoN5

open V

/-! # Helpers: the chosen clique vertex lies in the corresponding red block -/

lemma A1_mem_redBlock1_of_red
    (color : Sym2 V → Fin 2) (i : Fin 2)
    (_hAdj : G.Adj apex (A1 i))
    (hRed : color (s(apex, A1 i)) = 1) :
    A1 i ∈ redBlock1 color := by
  classical
  -- First: `A1 i` is a red neighbor of `apex`.
  have hRN : A1 i ∈ redNeighbors color := by
    -- `neighborFinset` membership + color=1
    have : A1 i ∈ G.neighborFinset apex := by simp
    exact Finset.mem_filter.mpr ⟨this, by simpa⟩
  -- Second: it's in block 1.
  have hB : inBlock1 (A1 i) := by simp [inBlock1]
  -- Filter once more.
  simpa [redBlock1] using Finset.mem_filter.mpr ⟨hRN, hB⟩

lemma A2_mem_redBlock2_of_red
    (color : Sym2 V → Fin 2) (i : Fin 3)
    (_hAdj : G.Adj apex (A2 i))
    (hRed : color (s(apex, A2 i)) = 1) :
    A2 i ∈ redBlock2 color := by
  classical
  have hRN : A2 i ∈ redNeighbors color := by
    have : A2 i ∈ G.neighborFinset apex := by simp
    exact Finset.mem_filter.mpr ⟨this, by simpa⟩
  have hB : inBlock2 (A2 i) := by simp [inBlock2]
  simp [redBlock2, hRN, isA1, isB1]

/-! # Triangle-or-star from Block 1 -/

/-- If Block 1 has at least 6 red apex-neighbors, and one of them is {lean}`A1 i` with a red edge
from {name}`apex`, then either we have a red triangle, or a blue `K_{1,5}` centered at {lean}`A1 i`. -/
lemma triangle_or_blueStar_from_block1
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock1 color).card)
    (i : Fin 2)
    (hAdj : G.Adj apex (A1 i))
    (hRedApexA1 : color (s(apex, A1 i)) = 1) :
    hasMonoTriangle G color 1 ∨ hasMonoStar G color 0 5 := by
  classical
  -- Put `y0 := A1 i` into `redBlock1`.
  have hy0_in : A1 i ∈ redBlock1 color := A1_mem_redBlock1_of_red color i hAdj hRedApexA1
  -- We want 5 vertices in `redBlock1 \ {A1 i}`.
  have h5 :
    5 ≤ ((redBlock1 color).erase (A1 i)).card := by
    -- `card (erase y0) + 1 = card`  ⇒  `card (erase y0) ≥ 5` from `card ≥ 6`
    have hcard :
        ((redBlock1 color).erase (A1 i)).card + 1 = (redBlock1 color).card :=
      Finset.card_erase_add_one hy0_in
    -- turn `6 ≤ RHS` into `5 ≤ LHS`
    have : 6 ≤ ((redBlock1 color).erase (A1 i)).card + 1 := by simpa [hcard] using h6
    exact (Nat.succ_le_succ_iff.mp this)
  -- Pick any 5-element subset `T` of those.
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq ((redBlock1 color).erase (A1 i)) h5

  -- Either some `y ∈ T` makes the edge `(A1 i,y)` red (→ triangle), or all are blue (→ star).
  classical
  by_cases hTri : ∃ y ∈ T, color (s(A1 i, y)) = 1
  · rcases hTri with ⟨y, hyT, hyRedA1y⟩
    -- Facts from membership: `y ≠ A1 i`, `y ∈ redBlock1`.
    have hy_erase : y ∈ (redBlock1 color).erase (A1 i) := hTsub hyT
    have hy_ne : y ≠ A1 i := (Finset.mem_erase.mp hy_erase).1
    have hy_in : y ∈ redBlock1 color := (Finset.mem_erase.mp hy_erase).2
    -- Unpack `redBlock1` membership to get that `y` is a red neighbor of `apex` in block 1.
    rcases Finset.mem_filter.1 hy_in with ⟨hy_RN, hy_block1⟩
    rcases Finset.mem_filter.1 hy_RN with ⟨hyAdjApex, hyRedApexY⟩
    -- `A1 i` is adjacent to every other vertex in Block 1 (clique-to-A1, clique-to-B1).
    have hyAdjA1Y : G.Adj (A1 i) y := by
      cases y with
      | A1 j =>
          -- `j ≠ i` because `y ≠ A1 i`
          have hij : j ≠ i := by
            intro h; exact hy_ne (by simp [h])
          -- use `adj_A1A1 : Adj (A1 i) (A1 j) ↔ i ≠ j`
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A1A1, this]
      | B1 _  => simp [adj_A1B1]
      | A2 _  => cases hy_block1       -- impossible
      | B2 _  => cases hy_block1       -- impossible
      | apex  => cases hy_block1       -- impossible
    -- Build the red triangle: apex — A1 i — y — apex.
    refine Or.inl ?triangle
    refine ⟨apex, A1 i, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hAdj]
    · exact hyAdjA1Y
    · simpa using hyAdjApex
    · simpa using hRedApexA1
    · exact hyRedA1y
    · simpa using hyRedApexY
  · -- No red `(A1 i,y)` with `y ∈ T` ⇒ all `(A1 i,y)` are blue.
    have hAllBlue : ∀ {y}, y ∈ T → color (s(A1 i, y)) = 0 := by
      intro y hy
      have h1 : color (s(A1 i, y)) ≠ 1 := by
        intro contra; exact hTri ⟨y, hy, contra⟩
      -- In `Fin 2`, being not `1` is being `0`.
      -- (If you prefer, keep and reuse your earlier lemma `fin2_eq_one_iff_ne_zero`.)
      have : color (s(A1 i, y)) = 0 ∨ color (s(A1 i, y)) = 1 := by
        grind
      exact this.resolve_right h1
    -- Show `A1 i ∉ T`.
    have hnotin : A1 i ∉ T := by
      intro hx
      have : A1 i ∈ (redBlock1 color).erase (A1 i) := hTsub hx
      simp at this
    -- Adjacency `(A1 i,y)` for `y ∈ T`:
    have hAdjAll : ∀ {y}, y ∈ T → G.Adj (A1 i) y := by
      intro y hy
      have hy_erase : y ∈ (redBlock1 color).erase (A1 i) := hTsub hy
      have hy_ne : y ≠ A1 i := (Finset.mem_erase.mp hy_erase).1
      have hy_in : y ∈ redBlock1 color := (Finset.mem_erase.mp hy_erase).2
      rcases Finset.mem_filter.1 hy_in with ⟨_, hy_block1⟩
      -- same case split as above
      cases y with
      | A1 j =>
          have hij : j ≠ i := by intro h; exact hy_ne (by simp [h])
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A1A1, this]
      | B1 _  => simp [adj_A1B1]
      | A2 _  => simp [isA1, isB1] at hy_block1
      | B2 _  => simp [isA1, isB1] at hy_block1
      | apex  => simp [G, GAdj]
    -- We have a blue star of size 5 centered at `A1 i` with leaf-set `T`.
    refine Or.inr ?star
    refine ⟨A1 i, T, by simp [hTcard], hnotin, ?_⟩
    intro y hy
    exact ⟨hAdjAll hy, hAllBlue hy⟩

/-! # Triangle-or-star from Block 2 (same proof pattern) -/

lemma triangle_or_blueStar_from_block2
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock2 color).card)
    (i : Fin 3)
    (hAdj : G.Adj apex (A2 i))
    (hRedApexA2 : color (s(apex, A2 i)) = 1) :
    hasMonoTriangle G color 1 ∨ hasMonoStar G color 0 5 := by
  classical
  have hy0_in : A2 i ∈ redBlock2 color := A2_mem_redBlock2_of_red color i hAdj hRedApexA2
  have h5 :
    5 ≤ ((redBlock2 color).erase (A2 i)).card := by
    have hcard :
        ((redBlock2 color).erase (A2 i)).card + 1 = (redBlock2 color).card :=
      Finset.card_erase_add_one hy0_in
    have : 6 ≤ ((redBlock2 color).erase (A2 i)).card + 1 := by simpa [hcard] using h6
    exact (Nat.succ_le_succ_iff.mp this)
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq ((redBlock2 color).erase (A2 i)) h5

  by_cases hTri : ∃ y ∈ T, color (s(A2 i, y)) = 1
  · rcases hTri with ⟨y, hyT, hyRedA2y⟩
    have hy_erase : y ∈ (redBlock2 color).erase (A2 i) := hTsub hyT
    have hy_ne : y ≠ A2 i := (Finset.mem_erase.mp hy_erase).1
    have hy_in : y ∈ redBlock2 color := (Finset.mem_erase.mp hy_erase).2
    rcases Finset.mem_filter.1 hy_in with ⟨hy_RN, hy_block2⟩
    rcases Finset.mem_filter.1 hy_RN with ⟨hyAdjApex, hyRedApexY⟩
    have hyAdjA2Y : G.Adj (A2 i) y := by
      cases y with
      | A2 j =>
          have hij : j ≠ i := by intro h; exact hy_ne (by simp [h])
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A2A2, this]
      | B2 _  => simp [adj_A2B2]
      | A1 _  => simp [isA1] at hy_block2
      | B1 _  => simp [isB1] at hy_block2
      | apex  => simp [G,GAdj]
    refine Or.inl ?triangle
    refine ⟨apex, A2 i, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hAdj]
    · exact hyAdjA2Y
    · aesop
    · simpa using hRedApexA2
    · exact hyRedA2y
    · simpa using hyRedApexY
  ·
    have hAllBlue : ∀ {y}, y ∈ T → color (s(A2 i, y)) = 0 := by
      intro y hy
      have h1 : color (s(A2 i, y)) ≠ 1 := by
        intro contra; exact hTri ⟨y, hy, contra⟩
      have : color (s(A2 i, y)) = 0 ∨ color (s(A2 i, y)) = 1 := by grind
      exact this.resolve_right h1
    have hnotin : A2 i ∉ T := by
      intro hx
      have : A2 i ∈ (redBlock2 color).erase (A2 i) := hTsub hx
      simp at this
    have hAdjAll : ∀ {y}, y ∈ T → G.Adj (A2 i) y := by
      intro y hy
      have hy_erase : y ∈ (redBlock2 color).erase (A2 i) := hTsub hy
      have hy_ne : y ≠ A2 i := (Finset.mem_erase.mp hy_erase).1
      have hy_in : y ∈ redBlock2 color := (Finset.mem_erase.mp hy_erase).2
      rcases Finset.mem_filter.1 hy_in with ⟨_, hy_block2⟩
      cases y with
      | A2 j =>
          have hij : j ≠ i := by intro h; exact hy_ne (by simp [h])
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A2A2, this]
      | B2 _  => simp [adj_A2B2]
      | A1 _  => simp [isA1] at hy_block2
      | B1 _  => simp [isB1] at hy_block2
      | apex  => simp [G, GAdj]
    refine Or.inr ?star
    refine ⟨A2 i, T, by simp [hTcard], hnotin, ?_⟩
    intro y hy
    exact ⟨hAdjAll hy, hAllBlue hy⟩

/-! # Final step: no blue `K_{1,5}` ⇒ a red triangle -/

/-- **Main step (n=5):** If there is no blue `K_{1,5}`, then the red color class contains a triangle. -/
theorem red_triangle_of_no_blue_star
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    hasMonoTriangle G color 1 := by
  classical
  -- One of the two blocks has ≥6 red neighbors from `apex`.
  have h6 := exists_block_receives_at_least_6_red color hNoBlueStar
  -- From that block, extract a clique vertex with a red edge from `apex`.
  rcases h6 with hB1 | hB2
  · -- Block 1 case
    rcases exists_red_A1_of_block1_ge6 color hB1 with ⟨i, hAdj, hRed⟩
    -- Either get triangle or (if star) contradict `hNoBlueStar`.
    rcases triangle_or_blueStar_from_block1 color hB1 i hAdj hRed with hTri | hStar
    · exact hTri
    · exact (hNoBlueStar hStar).elim
  · -- Block 2 case
    rcases exists_red_A2_of_block2_ge6 color hB2 with ⟨i, hAdj, hRed⟩
    rcases triangle_or_blueStar_from_block2 color hB2 i hAdj hRed with hTri | hStar
    · exact hTri
    · exact (hNoBlueStar hStar).elim

end PikhurkoN5

-- Final statement

namespace PikhurkoN5

theorem main : Pikhurko_n5_statement := by
  use V, G
  split_ands
  . exact edge_count_44
  intro color
  have := red_triangle_of_no_blue_star color
  grind

end PikhurkoN5
