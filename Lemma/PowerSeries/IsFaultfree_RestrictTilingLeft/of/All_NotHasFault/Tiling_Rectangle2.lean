import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[restrict_tiling_left_is_faultfree_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (hk : hasFault n T k)
  (hmin : ∀ j, j < k → ¬hasFault n T j) :
-- imply
  isFaultfree k (restrictTilingLeft n T k hk) := by
-- proof
  constructor
  · exact hk.1
  · intro j hfault_restr
    -- We need to show False (i.e., no fault at j in the restricted tiling)
    -- A fault at j in the restricted tiling would imply a fault at j in T
    -- But j < k and hmin says there's no fault at j in T
    have hj_lt : j < k := hfault_restr.2.1
    have hj_lt_n : j < n := Nat.lt_trans hj_lt hk.2.1
    have hfault_T : hasFault n T j := by
      refine ⟨hfault_restr.1, hj_lt_n, ?_⟩
      intro d hd
      cases d with
      | horizontal i jj =>
        -- If d is in T.dominos, it's either in left part or right part
        have hlr := domino_left_or_right_at_fault hk (Domino.horizontal i jj) hd
        rcases hlr with hleft | hright
        · -- d is in left part, so it's in the restricted tiling
          have hd_restr : Domino.horizontal i jj ∈ (restrictTilingLeft n T k hk).dominos := by
            simp only [restrictTilingLeft, Set.mem_sep_iff]
            exact ⟨hd, hleft⟩
          exact hfault_restr.2.2 (Domino.horizontal i jj) hd_restr
        · -- d is in right part (x ≥ k+1), so i ≥ k+1 > j, hence i ≥ j+1
          simp only [Domino.inRightPart, Domino.toShape] at hright
          have hi := hright (i, jj) (by simp)
          have hj_lt_k : (j : ℤ) < k := by exact_mod_cast hj_lt
          right
          -- Need to show i ≥ j + 1
          -- We have hi : i ≥ k + 1 and hj_lt : j < k
          -- So i ≥ k + 1 > k > j, hence i ≥ j + 1
          omega
      | vertical _ _ => trivial
    exact hmin j hj_lt hfault_T


-- created on 2026-10-20
