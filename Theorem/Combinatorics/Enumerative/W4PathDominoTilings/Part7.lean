module
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part9
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/
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
