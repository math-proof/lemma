import Mathlib
import Lemma.Definitions.Def_ModularCurve_JZeroNeronData
import Lemma.Definitions.Def_ModularCurve_MazurPrincipleCore

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def primesOf (M : ℕ) : Finset Nat.Primes := (M.primeFactors).subtype Nat.Prime

theorem mem_primesOf {M : ℕ} [NeZero M] (ℓ : Nat.Primes) : ℓ ∈ primesOf M ↔ (ℓ : ℕ) ∣ M := by
  have h1 := Finset.mem_subtype (s := M.primeFactors) (a := ℓ)
  refine h1.trans ?_
  rw [Nat.mem_primeFactors]
  exact ⟨fun h => h.2.1, fun h => ⟨ℓ.2, h, NeZero.ne _⟩⟩

structure JZeroNeronAtPData (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    extends JZeroNeronData N q hqN A hA where

  toricRank : ℕ

  abelianRank : ℕ

  card_toric : ∀ m : ℕ, 0 < m → Nat.card ↥(toric m) = m ^ toricRank

  card_fin : ∀ m : ℕ, 0 < m → Nat.card ↥(fin m) = m ^ (toricRank + 2 * abelianRank)

  fin_heckeTorsion_detects_lowerLevel :
    HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    HeckeInputsAll N → HeckeOperatorsCommuteBar N →
      ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ((q : ℕ) : HeckeAlg) ∈ 𝔪 →
        ∀ x ∈ fin q, (letI := heckeModuleBar (N * q); x ∈ heckeTorsion (JZero (N * q)) 𝔪) →
          x ∉ toric q →
            (letI := heckeModuleBar N; HasLowerLevelTorsion (primesOf (N * q)) 𝔪 (JZero N))

def HasJZeroNeronAtPData (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPData N q hqN A hA)

end ModularCurve

end
