import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace Stickelberger

def exponentSet (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun c => 0 < c ∧ 2 * c < p


def eigenvalueScalar (p : ℕ) : ℕ := ∑ c ∈ exponentSet p, c

noncomputable def expUnit (p : ℕ) (c : ℕ) : (ZMod p)ˣ :=
  if h : Nat.Coprime c p then ZMod.unitOfCoprime c h else 1

variable {p : ℕ} {A : Type*} [AddCommGroup A] [Module (ZMod p) A]

noncomputable def stickelbergerEnd (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) :
    Module.End (ZMod p) A :=
  ∑ c ∈ exponentSet p, ρ (expUnit p c)⁻¹

def StickelbergerAnnihilates (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) : Prop :=
  ∀ a : A, stickelbergerEnd ρ a = 0

def IsOmegaEigenvector (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) (i : ℕ) (a : A) : Prop :=
  ∀ d : (ZMod p)ˣ, ρ d a = ((d : ZMod p) ^ i) • a

end Stickelberger
