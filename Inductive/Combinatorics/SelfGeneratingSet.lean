/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Lattice
import Def.Combinatorics.SelfGeneratingSet


namespace MetaMathlibExt

namespace SelfGeneratingSet

/-- Reachability from `seed` by a finite composition of generators in `F`. The constructor
`seed_mem` represents the empty composition. -/
inductive Gen (F : Finset (Nat → Nat)) (seed : Nat) : Nat → Prop where
  | seed_mem : Gen F seed seed
  | step (w : Nat) : Gen F seed w → ∀ f ∈ F, Gen F seed (f w)

end SelfGeneratingSet
end MetaMathlibExt
