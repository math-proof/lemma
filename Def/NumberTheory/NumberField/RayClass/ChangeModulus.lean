/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean -/

import Def.NumberTheory.NumberField.RayClass.CongruenceEquivalence
import Lemma.Nat.NumberField.RayClass.CongruenceEquivalence
/-!
# Change of modulus (ATLAS NumberTheoryI item N422 / Lemma 22.5)

Fixed-modulus equivalence criterion: for moduli with `m2 ∣ m1`, a congruence
subgroup at `m1` admits an equivalent congruence subgroup at the fixed modulus
`m2` if and only if it already contains the part of the `m2`-ray group that is
coprime to `m1`, i.e. `coprimeFractionalIdeals m1 ⊓ rayGroupAmbient m2 ≤ C1`.

The definition `changeModulus` is the canonical witness: the pullback of `C1`
to the `m2`-coprime ideals joined with the `m2`-ray group, which is equivalent
to `C1` whenever the criterion holds.
-/


noncomputable section

open scoped nonZeroDivisors

namespace NumberField.Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Ambient ray group in the ambient fractional-ideal units. -/
def rayGroupAmbient (m : Modulus K) : Subgroup ((FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  (rayGroup m).map (coprimeFractionalIdeals m).subtype

/-- Change of modulus by pullback joined with the ray group. -/
def changeModulus {m1 : Modulus K} (C1 : CongruenceSubgroup m1)
    (m2 : Modulus K) : CongruenceSubgroup m2 where
  toSubgroup :=
    C1.toAmbientSubgroup.comap (coprimeFractionalIdeals m2).subtype ⊔
      rayGroup m2
  rayGroup_le := le_sup_right

end NumberField.Modulus
end
