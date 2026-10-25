import Lemma.ModularCurve.ModuliPoint

set_option autoImplicit false

namespace ModularCurve

def ssJSet (p : ℕ) (K : Type*) [Field K] [DecidableEq K] : Set K :=
  {j | ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
    ∀ P : W.toAffine.Point, p • P = 0 → P = 0}


def ModuliPoint.IsSupersingular (p : ℕ) {N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (x : ModuliPoint N K) : Prop :=
  x.j ∈ ssJSet p K

def ssLocus (p N : ℕ) (K : Type*) [Field K] [DecidableEq K] : Set (ModuliPoint N K) :=
  {x | x.IsSupersingular p}

end ModularCurve
