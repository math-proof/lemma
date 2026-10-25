import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Lemma.FLTPrelim.FreyPackage

set_option autoImplicit false

namespace FreyCurve

open FreyPackage

def c₄Int (P : FreyPackage) : ℤ :=
  (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2

def _root_.WeierstrassCurve.IsSemistableAt (W : WeierstrassCurve ℚ) (q : ℕ) : Prop :=
  padicValRat q W.Δ = 0 ∨ padicValRat q W.c₄ = 0

def _root_.WeierstrassCurve.IsSemistable (W : WeierstrassCurve ℚ) : Prop :=
  ∀ q : ℕ, q.Prime → W.IsSemistableAt q

end FreyCurve
