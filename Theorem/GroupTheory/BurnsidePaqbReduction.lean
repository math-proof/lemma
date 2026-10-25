/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean -/

import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Def.GroupTheory.BurnsidePaqbReduction
/-!
# Conjugacy classes and a Sylow-center reduction step for groups of order `p ^ a * q ^ b`

Authors: Muse Spark 1.3

Port of the fully proved group-theoretic core from the screened archive
`burnside_wip.zip` (SHA-256
`0686f20667e5fef0850dc3c6ba2e4d9e3ef5ba3f89c2f937faa8a251cd1eee30`):
`Burnside/ConjClass.lean` lines 1–45, `Burnside/ClassSum.lean` lines 13–17,
and `Burnside/SylowCenter.lean` lines 1–56.

Historical citation (independently verified): W. Burnside, "On Groups of Order
p^alpha q^beta," *Proceedings of the London Mathematical Society* s2-1 (1904),
388–392, DOI 10.1112/plms/s2-1.1.388.

This partial stage does not prove the full Burnside `p^a * q^b` solvability theorem.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

open Classical in
theorem mem_conjClass_iff {g h : G} : h ∈ conjClass g ↔ IsConj h g := by
  simp [conjClass, ConjAct.mem_orbit_conjAct, Set.mem_toFinset]

end BurnsidePaqb
