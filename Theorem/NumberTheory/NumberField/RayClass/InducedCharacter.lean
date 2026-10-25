/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean -/

import Def.NumberTheory.NumberField.RayClass.Character
import Lemma.Nat.NumberField.RayClass.Character
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Induced ray class characters (N428 Definition 22.12)

If `m1 ∣ m2`, a ray class character at `m2` is induced by one at `m1`
when their values agree on ideals coprime to `m2` under level change.
A character is primitive when it is induced only from the same modulus.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K] {m1 m2 : Modulus K}

/-- Finite exponents are monotone under modulus divisibility. -/
theorem finiteExponent_le_of_dvd (h : m1 ∣ m2)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    finiteExponent m1 v ≤ finiteExponent m2 v := by
  have hfin := ((dvd_unfold m1 m2).mp h).1
  have hne : (m2.finitePart : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa using mem_nonZeroDivisors_iff_ne_zero.mp m2.finitePart.property
  unfold finiteExponent
  exact FractionalIdeal.count_mono K v (FractionalIdeal.coeIdeal_ne_zero.mpr hne)
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hfin)

theorem coprime_le_of_dvd (h : m1 ∣ m2) :
    coprimeFractionalIdeals m2 ≤ coprimeFractionalIdeals m1 := by
  intro u hu v hv
  exact hu v (le_trans ((dvd_unfold m1 m2).mp h).1 hv)

end Modulus
end NumberField
