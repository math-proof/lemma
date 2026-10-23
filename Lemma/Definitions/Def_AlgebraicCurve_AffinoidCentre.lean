import Lemma.Definitions.Def_AlgebraicCurve_SemistableChartsComap

set_option autoImplicit false

namespace AlgebraicCurve

open IsLocalRing
open scoped Pointwise

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def ComponentChart.tubeBounded (C : ComponentChart A F Fbar) (f : F) : Prop :=
  ∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A

def ComponentChart.HasAffinoidLifting (C : ComponentChart A F Fbar) (N : Finset (Place (ResidueField A) Fbar)) : Prop :=
  (∀ f : F, C.tubeBounded f → f ∈ C.integers) ∧
  (∀ g : Fbar, (∀ Q : Place (ResidueField A) Fbar, Q ∉ N → g ∈ Q.toValuationSubring) →
    ∃ (f : F) (hf : f ∈ C.integers), C.tubeBounded f ∧ C.residue ⟨f, hf⟩ = g) ∧
  ∀ h : F, h ∈ C.integers → ∃ (r s : F) (hs : s ∈ C.integers),
    C.tubeBounded r ∧ C.tubeBounded s ∧ C.residue ⟨s, hs⟩ ≠ 0 ∧ h * s = r

def ComponentChart.regOff (N : Finset (Place (ResidueField A) Fbar)) : Subring Fbar :=
  ⨅ (Q : Place (ResidueField A) Fbar) (_ : Q ∉ N), Q.toValuationSubring.toSubring

def ComponentChart.HasPlaceDictionary (N : Finset (Place (ResidueField A) Fbar)) : Prop :=
  (∀ 𝔪 : Ideal (ComponentChart.regOff (A := A) N), 𝔪.IsMaximal →
    ∃! Q : Place (ResidueField A) Fbar, Q ∉ N ∧ ∀ g : ComponentChart.regOff (A := A) N, g ∈ 𝔪 ↔ (g : Fbar) = 0 ∨ 0 < Q.ord (g : Fbar)) ∧
  ∀ Q : Place (ResidueField A) Fbar, Q ∉ N →
    ∃ 𝔪 : Ideal (ComponentChart.regOff (A := A) N), 𝔪.IsMaximal ∧
      ∀ g : ComponentChart.regOff (A := A) N, g ∈ 𝔪 ↔ (g : Fbar) = 0 ∨ 0 < Q.ord (g : Fbar)

def ComponentChart.IsCentre (C : ComponentChart A F Fbar) (N : Finset (Place (ResidueField A) Fbar)) (O : ValuationSubring F)
    (Q : Place (ResidueField A) Fbar) : Prop :=
  Q ∉ N ∧ ∀ (f : F) (hf : f ∈ C.integers), C.tubeBounded f →
    ((C.residue ⟨f, hf⟩ = 0 ∨ 0 < Q.ord (C.residue ⟨f, hf⟩)) ↔ ∃ h : f ∈ O, (⟨f, h⟩ : O) ∈ maximalIdeal O)

end AlgebraicCurve
