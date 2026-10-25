/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part3
open SimpleGraph


section

namespace MetaMathlibExt

instance tilingFintype : ∀ (m : ℕ) (S : Finset (Fin 4)), Fintype (Tiling m S)
  | 0, _ => PLift.fintypeProp _
  | (m + 1), _ =>
      @Sigma.instFintype _ _ (fun S =>
        @instFintypeProd _ _ (PLift.fintypeProp _)
          (@instFintypeProd _ _ (tilingFintype m S) (horizFintype _))) inferInstance

end MetaMathlibExt
end
