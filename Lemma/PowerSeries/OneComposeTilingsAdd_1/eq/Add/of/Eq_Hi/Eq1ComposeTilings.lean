import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[compose_tilings_prepend_width'_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (m first_width rest_width : ℕ)
  (first : Subtype (fun (T' : Tiling (Rectangle first_width 2)) => isFaultfree first_width T'))
  (rest : Fin m → (Σ w : ℕ, Subtype (fun (T' : Tiling (Rectangle w 2)) => isFaultfree w T')))
  (ts : Fin (m + 1) → (Σ w : ℕ, Subtype (fun (T' : Tiling (Rectangle w 2)) => isFaultfree w T')))
  (hrest : (composeTilings m rest).1 = rest_width)
  (hts : ts = fun i => if hi : i.val = 0 then ⟨first_width, first⟩ else rest ⟨i.val - 1, by omega⟩) :
-- imply
  (composeTilings (m + 1) ts).1 = first_width + rest_width := by
-- proof
  rw [composeTilings_prepend_width m first_width first rest ts hts]
  simp only [composeTilings] at hrest
  rw [hrest]


-- created on 2026-10-20
