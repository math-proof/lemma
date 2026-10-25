import Mathlib
import Lemma.FLTPrelim.FreyPackage
import Instance.ModularCurve_ArithmeticGalois

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

def JZeroTorsionFinite (M : ℕ) [NeZero M] (n : ℕ) : Prop :=
  Finite (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar M) n)

end ModularCurve

namespace FreyPackage

open ModularCurve

def MazurJZeroPTorsionFiniteFamily (P : FreyPackage) (q : ℕ) [NeZero q] : Prop :=
  ∀ (N : ℕ) [NeZero N], ¬ q ∣ N → JZeroTorsionFinite (N * q) P.p

end FreyPackage

end
