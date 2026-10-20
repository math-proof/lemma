import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[compose_tilings_prepend_width_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (m first_width : ℕ)
  (first : Subtype (fun (T' : Tiling (Rectangle first_width 2)) => isFaultfree first_width T'))
  (rest : Fin m → (Σ w : ℕ, Subtype (fun (T' : Tiling (Rectangle w 2)) => isFaultfree w T')))
  (ts : Fin (m + 1) → (Σ w : ℕ, Subtype (fun (T' : Tiling (Rectangle w 2)) => isFaultfree w T')))
  (hts : ts = fun i => if hi : i.val = 0 then ⟨first_width, first⟩ else rest ⟨i.val - 1, by omega⟩) :
-- imply
  (composeTilings (m + 1) ts).1 = first_width + ∑ j : Fin m, (rest j).1 := by
-- proof
  simp only [composeTilings, hts]
  rw [Fin.sum_univ_succ]
  -- `0 = 0` is propositionally True, not defeq True; use ↓reduceDIte
  simp only [Fin.val_zero, ↓reduceDIte, Fin.val_succ, Nat.add_one_ne_zero, Nat.add_sub_cancel]


-- created on 2026-10-20
