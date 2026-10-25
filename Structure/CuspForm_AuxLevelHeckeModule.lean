import Lemma.CohCarrier.Inst
import Instance.CuspForm_HeckeAlgebra
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Instance.CuspForm_AuxLevelHeckeModule

set_option autoImplicit false

noncomputable section

namespace CuspForm.AuxLevel

structure Gen (N r : ℕ) (S : Set ℕ) : Type where

  ℓ : ℕ
  prime : ℓ.Prime
  notMem : ℓ ∉ S
  not_dvd : ¬ ℓ ∣ N
  ne : ℓ ≠ r


end CuspForm.AuxLevel

end
