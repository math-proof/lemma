import Mathlib
import Instance.ExtEndgame_ProductionDatum
import Lemma.GroupCohomology.ContinuousH2
import Def.GroupCohomology_GaloisUnitsInflation
import Def.GroupCohomology_CyclicCarry

set_option autoImplicit false
noncomputable section
open CategoryTheory ExtCitation groupCohomology

namespace groupCohomology

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (q : Nat.Primes) [Fact ((q : ℕ)).Prime]

def IsLocalInv
    (f : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p) : Prop :=
  ∀ (u : (PadicAlgCl q)ˣ), (u : PadicAlgCl q) = padicEmbedding q ζ →
  ∀ (φ : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}) ≃ₐ[ℚ_[q]] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
    (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ),
    (∀ x : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}), (x : PadicAlgCl q) ^ ((q : ℕ) ^ p - 1) = 1 → (φ x : PadicAlgCl q) = (x : PadicAlgCl q) ^ (q : ℕ)) →
  ∀ (π : ((IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))ˣ), ((π : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) : PadicAlgCl q) = ((q : ℕ) : PadicAlgCl q) →
  ∀ (_ : Normal ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
    (z : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p)
    (hz : z ∈ levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))),
    ((fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) => Additive.ofMul (u ^ (z g).val))
      - unitsInflate₂ (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})
          (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) (Additive.ofMul π))
      ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) →
    f (continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨z, hz⟩) = 1

open Classical in

def localInv : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p :=
  if h : ∃ f, IsLocalInv p ζ q f ∧ ∀ f', IsLocalInv p ζ q f' → f' = f then Classical.choose h else 0

end groupCohomology

end
