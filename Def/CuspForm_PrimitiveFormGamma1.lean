import Mathlib
import Instance.FLTPrelim_Modularity

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups

namespace CuspForm

variable {M : ℕ} {k : ℤ}

def HasNebentypus (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → ∀ τ : UpperHalfPlane,
    g (γ • τ) =
      ε ((γ 1 1 : ℤ) : ZMod M) *
        ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * g τ)

def IsEigenformWith (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  qCoeff g 1 = 1 ∧
  (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
    qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∀ n : ℕ, qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n) ∧
  HasNebentypus ε g

def EigenpacketOccursAt (k : ℤ) (a e : ℕ → ℂ) (M' : ℕ) : Prop :=
  ∃ (ε' : DirichletCharacter ℂ M') (h : CuspForm (Gamma1 M') k),
    h ≠ 0 ∧ HasNebentypus ε' h ∧
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ε' (p : ZMod M') = e p ∧
      ∀ n : ℕ,
        qCoeff h (p * n) +
            ε' (p : ZMod M') * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff h (n / p) else 0) =
          a p * qCoeff h n

def IsPrimitiveForm (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  IsEigenformWith ε g ∧
    ∀ M' : ℕ, M' ∣ M → M' ≠ M →
      ¬ EigenpacketOccursAt k (fun n => qCoeff g n) (fun n => ε (n : ZMod M)) M'

end CuspForm
