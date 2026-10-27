import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[restrict_tiling_right_compose_tilings_dominos_eq_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
-- imply
  (restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2
        (ts ⟨0, by omega⟩).1 hfault).dominos =
      (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2.dominos := by
-- proof
  exact restrictTilingRight_composeTilings_dominos k hk ts hfault


-- created on 2026-10-20
