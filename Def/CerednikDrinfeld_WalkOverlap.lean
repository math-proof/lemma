import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace CerednikDrinfeld
namespace Mumford

variable {W : Type} [DecidableEq W] {𝒯 : SimpleGraph W}


def walkOverlap {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') : ℤ :=
  (P.darts.map fun d => ((Q.darts.count d : ℕ) : ℤ) - ((Q.darts.count d.symm : ℕ) : ℤ)).sum

end Mumford

end CerednikDrinfeld
