import Mathlib

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

universe u v

variable {F : Type u} [Field F] (k : Type v) [Field k] [Algebra F k]

def evalEvalBC (p : F[X][Y]) (x y : k) : k :=
  (p.map (mapRingHom (algebraMap F k))).evalEval x y

variable [DecidableEq k]

def IsRationallyRepresented (W₁ W₂ : WeierstrassCurve F)
    (α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point) : Prop :=
  ∃ (nX dX nY dY : F[X][Y]) (B : Set k), B.Finite ∧
    ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
      evalEvalBC k dX x y ≠ 0 ∧ evalEvalBC k dY x y ≠ 0 ∧
        ∃ h', α (.some x y h) =
          .some (evalEvalBC k nX x y / evalEvalBC k dX x y)
            (evalEvalBC k nY x y / evalEvalBC k dY x y) h'

def rationalHomSet (W₁ W₂ : WeierstrassCurve F) :
    Set ((W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point) :=
  {α | α = 0 ∨ IsRationallyRepresented k W₁ W₂ α}

def rationalEndSubring (W : WeierstrassCurve F) :
    Subring (AddMonoid.End (W.baseChange k).toAffine.Point) :=
  Subring.closure (rationalHomSet k W W)

end WeierstrassCurve

end
