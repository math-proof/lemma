module
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part3
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/
section

namespace MetaMathlibExt

-- Horizontal partner within layer `j`, or `a` itself if matched vertically.
noncomputable def horizFunNat (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) : Fin 4 → Fin 4 :=
  fun a =>
    if h : j < m then
      let i : Fin m := ⟨j, h⟩
      let p := partner m M hM (a, i)
      if p.2 = i then p.1 else a
    else a

end MetaMathlibExt
end
