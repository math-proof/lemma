/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean -/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Lattice
public import Inductive.Combinatorics.SelfGeneratingSet

@[expose] public section

namespace MetaMathlibExt

namespace SelfGeneratingSet

/-- The closure of `seed` under finite compositions of generators in `F`. -/
def GeneratedSet (F : Finset (Nat → Nat)) (seed : Nat) : Set Nat :=
  {y | Gen F seed y}

end SelfGeneratingSet
end MetaMathlibExt
