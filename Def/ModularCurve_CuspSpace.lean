import Mathlib
import Instance.ModularCurve_CuspSpace

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

noncomputable section

def ratPoint (a c : ℤ) : OnePoint ℚ :=
  if c = 0 then ∞ else (((a : ℚ) / (c : ℚ) : ℚ) : OnePoint ℚ)

variable (N : ℕ)

def Gamma0Q : Subgroup (GL (Fin 2) ℚ) := (Gamma0 N).map (mapGL ℚ)

abbrev CuspSpace : Type := MulAction.orbitRel.Quotient (Gamma0Q N) (OnePoint ℚ)

namespace CuspSpace

def mk (x : OnePoint ℚ) : CuspSpace N := ⟦x⟧

variable {N}

variable (N)

def fromCoset : SL(2, ℤ) ⧸ Gamma0 N → CuspSpace N :=
  Quotient.lift (fun g => mk N (mapGL ℚ g⁻¹ • ∞))
    (fun _ _ hab => mk_smul_infty_eq_of_mem N (QuotientGroup.leftRel_apply.mp hab))

def cuspDenomAux (x : OnePoint ℚ) : ℕ :=
  x.elim N fun q => Nat.gcd q.den N

variable {N}

variable (N)

def cuspDenom : CuspSpace N → ℕ :=
  Quotient.lift (cuspDenomAux N) (by
    rintro x y ⟨⟨g, γ, hγ, rfl⟩, rfl⟩
    exact cuspDenomAux_smul hγ y)

variable {N}

def NormalFormCriterion (N : ℕ) : Prop :=
  ∀ (a a' : ℤ) (e : ℕ), e ∣ N → IsCoprime a (e : ℤ) → IsCoprime a' (e : ℤ) →
    (mk N (ratPoint a e) = mk N (ratPoint a' e) ↔
      (a : ZMod (Nat.gcd e (N / e))) = (a' : ZMod (Nat.gcd e (N / e))))

def Classification (N : ℕ) : Prop :=
  Nonempty (CuspSpace N ≃ (d : N.divisors) × (ZMod (Nat.gcd d (N / (d : ℕ))))ˣ)

end CuspSpace

end

end ModularCurve

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

noncomputable section

def cuspWidthOfDenom (N d : ℕ) : ℕ := N / Nat.gcd (d ^ 2) N

namespace CuspSpace

variable {N : ℕ}

def cuspWidth (x : CuspSpace N) : ℕ := cuspWidthOfDenom N (cuspDenom N x)

end CuspSpace

end

end ModularCurve
