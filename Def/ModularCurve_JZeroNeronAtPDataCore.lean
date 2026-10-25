import Mathlib
import Def.ModularCurve_JZeroNeronAtPDataSameIdeal
import Structure.ModularCurve_JZeroNeronAtPDataCore

set_option autoImplicit false

noncomputable section

namespace ModularCurve


def HasJZeroNeronAtPDataCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataCore N q hqN A hA)

def JZeroNeronAtPDataSameIdeal.toCore {N q : ℕ} [NeZero N] [Fact q.Prime] {hqN : ¬ q ∣ N}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime q}
    (D : JZeroNeronAtPDataSameIdeal N q hqN A hA) : JZeroNeronAtPDataCore N q hqN A hA where
  toric := D.toric
  fin := D.fin
  finPart := D.finPart
  toric_le_fin := D.toric_le_fin
  fin_le_finPart := D.fin_le_finPart
  finPart_le_torsion := D.finPart_le_torsion
  finPart_hecke := D.finPart_hecke
  finPart_dec := D.finPart_dec
  inertia_toric := D.inertia_toric
  Φ := D.Φ
  spec := D.spec
  spec_ker := D.spec_ker
  spec_hecke := D.spec_hecke
  Φ_eisenstein := D.Φ_eisenstein
  raynaud := D.raynaud
  fin_heckeTorsion_detects_lowerLevel := D.fin_heckeTorsion_detects_lowerLevel
  fin_heckeTorsion_detects_lowerLevel_sameIdeal := D.fin_heckeTorsion_detects_lowerLevel_sameIdeal

end ModularCurve

end
