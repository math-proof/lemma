module

public import Lemma.ZMod.Inst
public import Instance.CuspForm_HeckeAlgebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Instance.CuspForm_AuxLevelHeckeModule

set_option autoImplicit false

public noncomputable section

namespace CuspForm.AuxLevel

structure Gen (N r : ℕ) (S : Set ℕ) : Type where

  ℓ : ℕ
  prime : ℓ.Prime
  notMem : ℓ ∉ S
  not_dvd : ¬ ℓ ∣ N
  ne : ℓ ≠ r


end CuspForm.AuxLevel

end
