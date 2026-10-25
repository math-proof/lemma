import Mathlib
import Structure.ModularCurve_JZeroNeronData
import Structure.ModularCurve_MazurPrincipleCore

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def primesOf (M : ℕ) : Finset Nat.Primes := (M.primeFactors).subtype Nat.Prime


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


end ModularCurve

end
