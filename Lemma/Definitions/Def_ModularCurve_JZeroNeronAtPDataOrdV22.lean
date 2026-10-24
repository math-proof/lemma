import Mathlib
import Lemma.Definitions.Def_ModularCurve_JZeroNeronAtPDataOrdCore

set_option autoImplicit false

noncomputable section

namespace ModularCurve

structure JZeroNeronAtPDataOrdV22 (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    extends JZeroNeronAtPDataOrdCore N q hqN A hA where

  toric_card_heckeTorsion_le : q ≠ 2 → HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ¬ IsEventuallyEisenstein 𝔪 → ((q : ℕ) : HeckeAlg) ∈ 𝔪 →
      Finite (HeckeAlg ⧸ 𝔪) →
      (letI := heckeModuleBar (N * q); Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero (N * q)) 𝔪) = 2) →
      Nat.card ↥(toric q ⊓ (letI := heckeModuleBar (N * q);
          (heckeTorsion (JZero (N * q)) 𝔪).toAddSubgroup)) ≤ Nat.card (HeckeAlg ⧸ 𝔪)

def HasJZeroNeronAtPDataOrdV22 (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataOrdV22 N q hqN A hA)

end ModularCurve

end
