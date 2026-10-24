/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/CongruenceEquivalence.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.CongruenceEquivalence
import Lemma.Nat.NumberField.RayClass.CongruenceEquivalence

open scoped nonZeroDivisors
open NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

-- Reflexivity.
example (P : NumberField.Modulus.CongruenceSubgroupPair K) :
    P.IsEquivalent P :=
  NumberField.Modulus.CongruenceSubgroupPair.IsEquivalent.refl P

-- Symmetry.
example {P Q : NumberField.Modulus.CongruenceSubgroupPair K}
    (h : P.IsEquivalent Q) : Q.IsEquivalent P :=
  h.symm

-- Exact unfolded intersection formula.
example (P Q : NumberField.Modulus.CongruenceSubgroupPair K) :
    (P.IsEquivalent Q ↔
      NumberField.Modulus.coprimeFractionalIdeals P.modulus ⊓
          Q.subgroup.toAmbientSubgroup =
        NumberField.Modulus.coprimeFractionalIdeals Q.modulus ⊓
          P.subgroup.toAmbientSubgroup) :=
  NumberField.Modulus.CongruenceSubgroupPair.isEquivalent_iff P Q

-- Both sides live in the common ambient subgroup type.
example (P : NumberField.Modulus.CongruenceSubgroupPair K) :
    Subgroup ((FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  P.subgroup.toAmbientSubgroup

example (P Q : NumberField.Modulus.CongruenceSubgroupPair K)
    (h : P.IsEquivalent Q) :
    NumberField.Modulus.coprimeFractionalIdeals P.modulus ⊓
        Q.subgroup.toAmbientSubgroup =
      NumberField.Modulus.coprimeFractionalIdeals Q.modulus ⊓
        P.subgroup.toAmbientSubgroup :=
  h
