/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

module

public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part3
@[expose] public section

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
