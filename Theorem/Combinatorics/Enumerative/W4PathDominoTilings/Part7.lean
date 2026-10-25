/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part9
open SimpleGraph


section

namespace MetaMathlibExt

theorem getS_top (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling (m + 1) S') :
    getS (m + 1) S' t m = S' := by
  cases t with
  | mk S snd =>
    cases snd with
    | mk _ rest =>
      simp only [getS, ite_true]

end MetaMathlibExt
end
