import Mathlib
import Lemma.Definitions.Def_ModularCurve_JZeroNeronAtPData

set_option autoImplicit false

noncomputable section

namespace ModularCurve

structure JZeroNeronAtPDataSameIdeal (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    extends JZeroNeronAtPData N q hqN A hA where

  fin_heckeTorsion_detects_lowerLevel_sameIdeal :
    HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    HeckeInputsAll N → HeckeOperatorsCommuteBar N →
      ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ((q : ℕ) : HeckeAlg) ∈ 𝔪 → heckeGen ⟨q, Fact.out⟩ ∉ 𝔪 →
        ∀ x ∈ fin q, (letI := heckeModuleBar (N * q); x ∈ heckeTorsion (JZero (N * q)) 𝔪) →
          x ∉ toric q →
            (letI := heckeModuleBar N; heckeTorsion (JZero N) 𝔪 ≠ ⊥)

def HasJZeroNeronAtPDataSameIdeal (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataSameIdeal N q hqN A hA)

end ModularCurve

end
