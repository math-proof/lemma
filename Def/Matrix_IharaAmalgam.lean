module
public import Def.Matrix_IharaIota
public import Mathlib.GroupTheory.PushoutI
public import Instance.IharaAmalgam


public section

namespace Ihara

open CongruenceSubgroup

open scoped MatrixGroups

def iharaEdge (N q : ℕ) : Fin 2 → (Gamma0 (N * q) →* Gamma0 N) :=
  ![ι₀ N q, ι₁ N q]

def iharaAmalgam (N q : ℕ) : Type :=
  Monoid.PushoutI (iharaEdge N q)

def iharaVertex (N q : ℕ) (i : Fin 2) : Gamma0 N →* iharaAmalgam N q :=
  Monoid.PushoutI.of (φ := iharaEdge N q) i

def iharaBase (N q : ℕ) : Gamma0 (N * q) →* iharaAmalgam N q :=
  Monoid.PushoutI.base (iharaEdge N q)

section Lift

variable {N q : ℕ} {K : Type*} [Monoid K]

def pairFamily (f₀ f₁ : Gamma0 N →* K) : (i : Fin 2) → (Gamma0 N →* K) :=
  ![f₀, f₁]

def iharaLift (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q)) :
    iharaAmalgam N q →* K :=
  Monoid.PushoutI.lift (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h)

end Lift

end Ihara
