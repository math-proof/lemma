/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Def.Combinatorics.IsogenyVolcano.Part2
set_option autoImplicit false

open BigOperators

/-!
# Isogeny volcanoes on multigraphs

This file defines symmetric multigraphs by edge multiplicity and the combinatorial structure of
an isogeny volcano. Loops are permitted. The degree counts a loop's multiplicity once, following
the outgoing-isogeny convention rather than the convention where an undirected loop counts twice.
-/


namespace IsogenyVolcano

variable {ℓ : ℕ} {C : IsogenyVolcano ℓ}

instance decPredIsSurface (C : IsogenyVolcano ℓ) :
    DecidablePred C.isSurface :=
  fun v => inferInstanceAs (Decidable (C.level v = 0))

end IsogenyVolcano
