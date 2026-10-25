/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part3
open SimpleGraph


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
