import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[count_of_weight_tilings_height2_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ) :
-- imply
  TilingsHeight2.countOfWeight tilingsHeight2_isFiniteType n = numTilings n 2 := by
-- proof
  -- This follows from the definition: elements of weight n are exactly tilings of R_{n,2}
  unfold WeightedSet.countOfWeight numTilings
  -- Show the set of elements of weight n is in bijection with tilings of Rectangle n 2
  have h_eq : {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n} =
              Set.range (fun T : Tiling (Rectangle n 2) => (⟨n, T⟩ : Σ m : ℕ, Tiling (Rectangle m 2))) := by
    ext ⟨m, T⟩
    simp only [TilingsHeight2, Set.mem_ofPred_eq, Set.mem_range, Sigma.mk.injEq]
    constructor
    · intro hm
      use hm.symm ▸ T
      exact ⟨hm.symm, by simp⟩
    · intro ⟨T', hm, hT⟩
      exact hm.symm
  have h_finite := tilingsHeight2_isFiniteType n
  have h_card : h_finite.toFinset.card = {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n}.ncard := by
    rw [Set.ncard]
    simp only [h_finite.encard_eq_coe_toFinset_card, ENat.toNat_natCast]
  rw [h_card, h_eq]
  have h_inj : Function.Injective (fun T : Tiling (Rectangle n 2) => (⟨n, T⟩ : Σ m : ℕ, Tiling (Rectangle m 2))) := by
    intro T1 T2 heq
    exact Sigma.mk.inj heq |>.2 |> eq_of_heq
  rw [Set.ncard_range_of_injective h_inj]


-- created on 2026-10-20
