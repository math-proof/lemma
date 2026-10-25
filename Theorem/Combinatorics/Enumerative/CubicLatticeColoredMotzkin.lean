/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR.Part2
import Lemma.Finset.Enumerative.ULDMotzkinNumberOfRankR
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Def.Combinatorics.Enumerative.CubicLatticeColoredMotzkin


namespace MetaMathlibExt

/-- Value of the flat color index. -/
theorem flatIndex_val (n : ℕ) (x : Fin (n + 1) × Bool)
    (h : ¬x.1 = Fin.last n) :
    (flatIndex n x h).val = x.1.val * 2 + (if x.2 then 1 else 0) := rfl

end MetaMathlibExt
