import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Elliptic functions
-/

namespace PeriodPair

/-- A function is lattice-periodic for `L` when every element of the lattice is a period. -/
def IsLatticePeriodic (L : PeriodPair) (f : ℂ → ℂ) : Prop :=
  ∀ ω : L.lattice, f.Periodic (ω : ℂ)

/-- An elliptic function for `L` is a meromorphic lattice-periodic function. -/
structure IsEllipticFunction (L : PeriodPair) (f : ℂ → ℂ) : Prop where
  meromorphic : Meromorphic f
  periodic : L.IsLatticePeriodic f

theorem isLatticePeriodic_const (L : PeriodPair) (c : ℂ) :
    L.IsLatticePeriodic fun _ ↦ c :=
  fun _ _ ↦ rfl

theorem IsEllipticFunction.const (L : PeriodPair) (c : ℂ) :
    L.IsEllipticFunction fun _ ↦ c :=
  ⟨Meromorphic.const c, isLatticePeriodic_const L c⟩

theorem IsEllipticFunction.add {L : PeriodPair} {f g : ℂ → ℂ}
    (hf : L.IsEllipticFunction f) (hg : L.IsEllipticFunction g) :
    L.IsEllipticFunction (f + g) :=
  ⟨hf.meromorphic.add hg.meromorphic, fun ω ↦ (hf.periodic ω).add (hg.periodic ω)⟩

theorem IsEllipticFunction.mul {L : PeriodPair} {f g : ℂ → ℂ}
    (hf : L.IsEllipticFunction f) (hg : L.IsEllipticFunction g) :
    L.IsEllipticFunction (f * g) :=
  ⟨hf.meromorphic.mul hg.meromorphic, fun ω ↦ (hf.periodic ω).mul (hg.periodic ω)⟩

end PeriodPair
