
import Mathlib.Algebra.Ring.Defs

namespace MetaMathlibExt


/-- Plain L-additive predicate on a ring: `IsLAdditive f` means
    `f (m * n) = f m * n + f n * m` for all `m n`.
    Concept ID `jis_term_bfd3fbfcad54dede5f5564d5`,
    source ID `jis_source_e693bb8c36ef38f1abdf6e18`, lines 215-225. -/
def IsLAdditive {K : Type*} [Ring K] (f : K → K) : Prop :=
  ∀ m n, f (m * n) = f m * n + f n * m


end MetaMathlibExt
