import Mathlib
import Def.ModularCurve_XHDiamondModL
import Lemma.ModularCurve.QExpFrobeniusModL
import Instance.ModularCurve_HeckeDifferential
import Lemma.AlgebraicCurve.PolarDifferentials
import Def.ModularCurve_SupersingularModuli
import Instance.CuspForm_TwoCuspLattice

set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve IntermediateField CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

section Supersingular

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ)

end Supersingular

section Decimate

variable (K : Type*) [Field K] (p : ℕ) [NeZero p]

end Decimate

section FrobPush

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [NeZero p]

end FrobPush

section HeckeDiff

variable (K : Type*) [Field K] (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]

end HeckeDiff

section DiamondDiff

variable (K : Type*) [Field K] (N : ℕ) (H' : Subgroup (ZMod N)ˣ)

end DiamondDiff

section GenFamily

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

end GenFamily

section TwoComponent

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime] [CharP K p]

end TwoComponent

section PairOperators

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

end PairOperators

section GenPair

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (S : Set ℕ)

end GenPair

end ModularCurve

namespace CuspForm

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ)

abbrev intIdeal : Ideal (⊥ : Subring ℂ) :=
  Ideal.span {(p : (⊥ : Subring ℂ))}

end CuspForm

namespace ModularCurve

open scoped TensorProduct

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  [Algebra (ZMod p) K]

end ModularCurve

end
