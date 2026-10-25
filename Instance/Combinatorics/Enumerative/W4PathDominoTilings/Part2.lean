/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part2
open SimpleGraph


section

namespace MetaMathlibExt

instance horizFintype (U : Finset (Fin 4)) : Fintype (HorizPairing U) :=
  Subtype.fintype _

end MetaMathlibExt
end
