module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Abbrev.Analysis.InnerProductSpace.EuclideanVec
public import Abbrev.Analysis.Normed.Lp.LpSpace

@[expose] public section

namespace LpSpace

variable {p d : ℕ}

-- the same coordinates read in the Euclidean space (rl: `toL2`)
def toL2 (x : LpSpace p d) : EuclideanVec d :=
  WithLp.toLp 2 (WithLp.ofLp x)

-- read Euclidean coordinates as an ℓ^p vector (inverse of `toL2`; rl: implicit, the types coincide there)
def ofL2 (p : ℕ) (x : EuclideanVec d) : LpSpace p d :=
  WithLp.toLp p (WithLp.ofLp x)

end LpSpace
