import Mathlib
import Def.ModularCurve_WeierstrassLevelCarrier

set_option autoImplicit false

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type*} [CommRing T] (W : WeierstrassCurve T)


structure IsCyclicKernel (N : ℕ) (h : T[X]) : Prop where

  natDegree_le : h.natDegree ≤ (N - 1) / 2

  coeff_eq_one : h.coeff ((N - 1) / 2) = 1

  dvd_preΨ : h ∣ W.preΨ N

  dvd_smulNumerator : ∀ a : ℕ, 2 ≤ a → a ≤ (N - 1) / 2 → h ∣ W.smulNumerator a ((N - 1) / 2) h


section Map

variable {T' : Type*} [CommRing T'] (f : T →+* T')


end Map


end WeierstrassCurve

end
