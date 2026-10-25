import Mathlib
import Structure.FLTPrelim_FreyPackage

set_option autoImplicit false

namespace FreyPackage

structure IsConductorLevel (P : FreyPackage) (N : ℕ) : Prop where

  pos : 0 < N

  squarefree : Squarefree N

  support : ∀ q : ℕ, q.Prime → q ∣ N → (q : ℤ) ∣ P.a * P.b * P.c

end FreyPackage
