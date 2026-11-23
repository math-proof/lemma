module

public import Mathlib
public import Theorem.WeierstrassCurve.ModuliPoint
public import Theorem.WeierstrassCurve.MapPoint

@[expose] public section

noncomputable section

namespace ModularCurve

open WeierstrassCurve WeierstrassCurve.Affine

set_option autoImplicit false

universe u v w

section Map

variable {L : Type u} {L' : Type v} [Field L] [Field L']
variable [DecidableEq L] [DecidableEq L']

omit [DecidableEq L] [DecidableEq L'] in

variable {N : ℕ}

def Gamma0Pair.map (σ : L →+* L') (P : Gamma0Pair N L) : Gamma0Pair N L' where
  toCurve := P.toCurve.map σ
  isElliptic := inferInstance
  gen := WeierstrassCurve.mapPoint σ (W₀ := P.toCurve) P.gen
  addOrderOf_gen := (WeierstrassCurve.addOrderOf_mapPoint σ P.gen).trans P.addOrderOf_gen

def ModuliPoint.map (σ : L →+* L') : ModuliPoint N L → ModuliPoint N L' :=
  Quot.lift (fun P => (Quot.mk _ (P.map σ) : ModuliPoint N L'))
    fun _ _ h => Quot.sound (Gamma0Pair.Step.map σ h)

end Map


section Bridge

variable {L L' : Type} [Field L] [Field L'] [DecidableEq L] [DecidableEq L'] {N : ℕ}

omit [DecidableEq L] [DecidableEq L'] in
end Bridge

end ModularCurve

end
