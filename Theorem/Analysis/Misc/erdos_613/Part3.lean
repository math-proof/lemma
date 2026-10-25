import Mathlib
import Def.Analysis.Misc.erdos_613.Part4
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-- If there is no blue `K_{1,5}`, then the apex has at most 4 blue neighbors. -/
lemma blueNeighbors_card_le_4
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    (blueNeighbors color).card ≤ 4 := by
  classical
  -- Suppose ≥5 blue neighbors; extract a 5-subset and get a blue star.
  by_contra hle
  have hge : 5 ≤ (blueNeighbors color).card :=
    Nat.succ_le_of_lt (lt_of_not_ge hle)
  obtain ⟨S, hSsubset, hScard⟩ :=
    Finset.exists_subset_card_eq (blueNeighbors color) hge

  -- `apex ∉ S` since `apex` is not its own neighbor.
  have hapex_notin : apex ∉ S := by
    have : apex ∉ G.neighborFinset apex := by
      -- No loops ⇒ apex not adjacent to itself ⇒ not in neighbor set.
      simp [SimpleGraph.neighborFinset]
    exact fun hx => this <| (by
      have hx' : apex ∈ blueNeighbors color := hSsubset hx
      -- Blue neighbors are a subset of neighbors.
      have : blueNeighbors color ⊆ G.neighborFinset apex :=
        by
          intro v hv
          exact Finset.mem_of_mem_filter _ hv
      exact this hx')

  -- All edges from `apex` to `S` are present and blue, so we have a blue K_{1,5}.
  have hstar : hasMonoStar G color 0 5 := by
    refine ⟨apex, S, hScard, hapex_notin, ?_⟩
    intro y hy
    have hy' : y ∈ blueNeighbors color := hSsubset hy
    have hy_in : y ∈ G.neighborFinset apex ∧ color (s(apex, y)) = 0 := by
      simpa [blueNeighbors] using hy'
    exact ⟨by simpa using hy_in.1, hy_in.2⟩

  exact hNoBlueStar hstar

/-- If there is no blue `K_{1,5}`, then at least {lean}`11` neighbors of {name}`apex` are red. -/
lemma red_from_apex_at_least_11
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    (redNeighbors color).card ≥ 11 := by
  classical
  -- Split neighbors of apex into blue vs. non-blue; identify non-blue with red.
  have hsplit :
      (blueNeighbors color).card
      + ((G.neighborFinset apex).filter (fun v => ¬ (color (s(apex, v)) = 0))).card
      = (G.neighborFinset apex).card := by
    simpa [blueNeighbors] using
      (Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset apex)
        (p := fun v => color (s(apex, v)) = 0))

  have hred_is_notblue :
      (G.neighborFinset apex).filter (fun v => ¬ (color (s(apex, v)) = 0))
      =
      redNeighbors color := by
    ext v; by_cases hv : v ∈ G.neighborFinset apex
    · -- On neighbors, “not blue” is “red”.
      simp [redNeighbors, hv, fin2_eq_one_iff_ne_zero]
    · simp [redNeighbors, hv]

  -- So blue + red = all neighbors = 15 (by `degree_apex`).
  have hsum : (blueNeighbors color).card + (redNeighbors color).card
              = (G.neighborFinset apex).card := by
    convert Finset.card_sdiff_add_card_eq_card _
    . simp only [←hred_is_notblue, blueNeighbors]
      ext v; grind
    . infer_instance
    simp [redNeighbors]

  have hdeg : (G.neighborFinset apex).card = 15 := by
    simp [degree_apex]

  have hblue_le_4 := blueNeighbors_card_le_4 color hNoBlueStar

  -- Turn `blue + red = 15` into `red = 15 - blue`.
  have hred_eq : (redNeighbors color).card
      = 15 - (blueNeighbors color).card := by
    have hsum' : (redNeighbors color).card + (blueNeighbors color).card = 15 := by
      simpa [Nat.add_comm, hdeg] using hsum
    have := congrArg (fun t => t - (blueNeighbors color).card) hsum'
    -- `(red + blue) - blue = 15 - blue` ⇒ `red = 15 - blue`.
    simpa [Nat.add_sub_cancel] using this

  -- Finally: `blue ≤ 4` ⇒ `15 - blue ≥ 11`.
  have : 11 ≤ 15 - (blueNeighbors color).card :=
    by grind

  -- Combine with `red = 15 - blue`.
  simpa [hred_eq] using this

end PikhurkoN5
