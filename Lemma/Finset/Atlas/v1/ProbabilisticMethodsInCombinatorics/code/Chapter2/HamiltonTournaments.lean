import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.HamiltonTournaments.Part2
open Finset Fintype SzeleTournament


namespace SzeleTournament

/--
[n_sub_one_le_card_edgeset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/HamiltonTournaments.lean)
-/
@[path]
lemma n_sub_one_le_card_edgeset
  {n : ℕ}
-- given
  (hn : n ≥ 1) :
-- imply
  n - 1 ≤ Fintype.card (EdgeSet n) := by
-- proof
  have hinj : Function.Injective (fun k : Fin (n - 1) =>
    (⟨(⟨k.val, by omega⟩, ⟨k.val + 1, by omega⟩), by
      exact Fin.mk_lt_mk.mpr (by omega)⟩ : EdgeSet n)) := by
    intro a b hab
    have h := congrArg (fun x => (x : EdgeSet n).val.1.val) hab
    exact Fin.ext h
  have := Fintype.card_le_of_injective _ hinj
  rwa [Fintype.card_fin] at this
/-- Total count via double counting: summing the number of Hamilton paths over all
tournaments equals $n! \cdot 2^{|E| - (n-1)}$, because for each of the $n!$ permutations
exactly $2^{|E| - (n-1)}$ tournaments admit it as a Hamilton path. -/

end SzeleTournament


-- created on 2026-10-23
