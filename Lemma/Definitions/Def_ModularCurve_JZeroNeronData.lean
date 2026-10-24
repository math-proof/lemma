import Mathlib
import Lemma.Definitions.Def_ModularCurve_HeckeModule
import Lemma.Definitions.Def_ModularCurve_HeckeInputsAll
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_ModularCurve_ToricMonodromyPart
import Lemma.Definitions.Def_GaloisRep_Flat

set_option autoImplicit false
noncomputable section

namespace ModularCurve

open ValuationSubring

section JZeroNeronAux
variable (M : ℕ) [NeZero M]

abbrev jZeroTorsion (m : ℕ) : AddSubgroup (JZero M) :=
  (Submodule.torsionBy ℤ (JZero M) (m : ℤ)).toAddSubgroup

def inertiaInvariantTorsion (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ) :
    AddSubgroup (JZero M) where
  carrier := {x | x ∈ jZeroTorsion M m ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x}
  zero_mem' := ⟨AddSubgroup.zero_mem _, fun σ _ => smul_zero σ⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨AddSubgroup.add_mem _ hx hy, fun σ hσ => by rw [smul_add, hx' σ hσ, hy' σ hσ]⟩
  neg_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨AddSubgroup.neg_mem _ hx, fun σ hσ => by rw [smul_neg, hx' σ hσ]⟩

end JZeroNeronAux

structure JZeroNeronData (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) : Type 1 where

  toric : ℕ → AddSubgroup (JZero (N * q))

  fin : ℕ → AddSubgroup (JZero (N * q))

  finPart : ℕ → AddSubgroup (JZero (N * q))
  toric_le_fin : ∀ m, toric m ≤ fin m
  fin_le_finPart : ∀ m, fin m ≤ finPart m
  finPart_le_torsion : ∀ m, finPart m ≤ jZeroTorsion (N * q) m

  toric_inf : ∀ m m' : ℕ, m ∣ m' → toric m = toric m' ⊓ jZeroTorsion (N * q) m
  fin_inf : ∀ m m' : ℕ, m ∣ m' → fin m = fin m' ⊓ jZeroTorsion (N * q) m
  finPart_inf : ∀ m m' : ℕ, m ∣ m' → finPart m = finPart m' ⊓ jZeroTorsion (N * q) m

  invariants_le_finPart : ∀ m, inertiaInvariantTorsion (N * q) A m ≤ finPart m

  finPart_eq_of_coprime : ∀ m, m.Coprime q → finPart m = inertiaInvariantTorsion (N * q) A m

  toric_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero (N * q)), x ∈ toric m →
    (letI := heckeModuleBar (N * q); t • x) ∈ toric m
  fin_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero (N * q)), x ∈ fin m →
    (letI := heckeModuleBar (N * q); t • x) ∈ fin m
  finPart_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero (N * q)), x ∈ finPart m →
    (letI := heckeModuleBar (N * q); t • x) ∈ finPart m

  toric_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ toric m, σ • x ∈ toric m
  fin_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ fin m, σ • x ∈ fin m
  finPart_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ finPart m, σ • x ∈ finPart m

  inertia_toric : ∀ (m : ℕ), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (c : ℕ),
    (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) → ∀ x ∈ toric m, σ • x = c • x

  inertia_unipotent : ∀ (m : ℕ), m.Coprime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
    ∀ x ∈ jZeroTorsion (N * q) m, σ • x - x ∈ toric m

  abq : ∀ m : ℕ, m.Coprime q → (↥(fin m) →+ (JZero N × JZero N))

  abq_ker : ∀ (m : ℕ) (hm : m.Coprime q) (x : ↥(fin m)), abq m hm x = 0 ↔ (x : JZero (N * q)) ∈ toric m

  abq_range : ∀ (m : ℕ) (hm : m.Coprime q),
    (abq m hm).range = (Submodule.torsionBy ℤ (JZero N × JZero N) (m : ℤ)).toAddSubgroup

  abq_compat : ∀ (m m' : ℕ) (hm : m.Coprime q) (hm' : m'.Coprime q) (h : m ∣ m') (x : ↥(fin m))
    (hx : (x : JZero (N * q)) ∈ fin m'), abq m' hm' ⟨x, hx⟩ = abq m hm x

  abq_hecke : ∀ (m : ℕ) (hm : m.Coprime q) (ℓ : Nat.Primes), ¬ (ℓ : ℕ) ∣ N * q → ∀ (x : ↥(fin m)),
    abq m hm ⟨(letI := heckeModuleBar (N * q); heckeGen ℓ • (x : JZero (N * q))),
               fin_hecke m (heckeGen ℓ) x x.2⟩
      = (letI := heckeModuleBar N; (heckeGen ℓ • (abq m hm x).1, heckeGen ℓ • (abq m hm x).2))

  abq_dec : ∀ (m : ℕ) (hm : m.Coprime q) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ A.decompositionSubgroup ℚ) (x : ↥(fin m)),
    abq m hm ⟨σ • (x : JZero (N * q)), fin_dec m σ hσ x x.2⟩ = (σ • (abq m hm x).1, σ • (abq m hm x).2)

  Φ : Type
  [instAddCommGroupΦ : AddCommGroup Φ]
  [instFiniteΦ : Finite Φ]
  [instModuleΦ : Module HeckeAlg Φ]

  spec : ∀ m : ℕ, (↥(finPart m) →+ Φ)

  spec_ker : ∀ (m : ℕ) (x : ↥(finPart m)), spec m x = 0 ↔ (x : JZero (N * q)) ∈ fin m

  spec_range : ∀ (m : ℕ), 0 < m → (spec m).range = (Submodule.torsionBy ℤ Φ (m : ℤ)).toAddSubgroup

  spec_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : ↥(finPart m)),
    spec m ⟨(letI := heckeModuleBar (N * q); t • (x : JZero (N * q))), finPart_hecke m t x x.2⟩ = t • spec m x

  spec_inertia : ∀ (m : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : ↥(finPart m)) (hσx : σ • (x : JZero (N * q)) ∈ finPart m), spec m ⟨_, hσx⟩ = spec m x

  spec_compat : ∀ (m m' : ℕ) (h : m ∣ m') (x : ↥(finPart m)) (hx : (x : JZero (N * q)) ∈ finPart m'),
    spec m' ⟨x, hx⟩ = spec m x

  Φ_eisenstein : HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q → ∀ φ : Φ, (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • φ = 0

  toric_frob_sq : ∀ (m : ℕ), m.Coprime q → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ q →
    ∀ x ∈ toric m, σ • σ • x = ((q : ℤ) ^ 2) • x

  toric_frob_hecke : HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    ∀ (m : ℕ), m.Coprime q → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ q →
      ∀ x ∈ toric m, σ • x = (letI := heckeModuleBar (N * q); (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, Fact.out⟩) • x)

  toric_monodromy : HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    ∀ (m : ℕ), m.Coprime q → ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → heckeTorsion Φ 𝔪 = ⊥ →
      ∀ x ∈ toric m, (letI := heckeModuleBar (N * q); x ∈ heckeTorsion (JZero (N * q)) 𝔪) →
        (letI := heckeModuleBar (N * q); x ∈ toricMonodromyPart (J := JZero (N * q)) q (A.inertiaSubgroupIn ℚ))

  raynaud : q ≠ 2 → ∀ (V : AddSubgroup (JZero (N * q))), V ≤ jZeroTorsion (N * q) q →
    ∀ (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
      [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
      [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
      (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥V),
      (∀ f g, e (f * g) = e f + e g) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) → ((e g : ↥V) : JZero (N * q)) = σ • ((e f : ↥V) : JZero (N * q))) →
      V ≤ finPart q

attribute [instance] JZeroNeronData.instAddCommGroupΦ JZeroNeronData.instFiniteΦ JZeroNeronData.instModuleΦ

def HasJZeroNeronData (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronData N q hqN A hA)

end ModularCurve

end
