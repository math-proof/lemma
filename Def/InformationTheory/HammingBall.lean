/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean -/

import Mathlib.InformationTheory.Hamming
open scoped BigOperators


namespace Hamming

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]

/-- The closed Hamming ball of radius `e` about `x`. -/
def ball (x : ι → F) (e : ℕ) : Finset (ι → F) :=
  Finset.univ.filter fun y => hammingDist x y ≤ e

def support (x y : ι → F) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ y i

def sphere (x : ι → F) (k : ℕ) : Finset (ι → F) :=
  Finset.univ.filter fun y => hammingDist x y = k

def supportFiber (x : ι → F) (s : Finset ι) : Finset (ι → F) :=
  Fintype.piFinset fun i => if i ∈ s then Finset.univ.erase (x i) else {x i}

end Hamming
