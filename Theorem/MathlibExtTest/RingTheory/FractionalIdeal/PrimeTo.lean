/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/FractionalIdeal/PrimeTo.lean -/


import Def.RingTheory.FractionalIdeal.PrimeTo.Part2
import Lemma.Int.FractionalIdeal.PrimeTo
open scoped nonZeroDivisors


noncomputable section

namespace FractionalIdeal

variable {A : Type*} [CommRing A] [IsDomain A]

example (J : Ideal A) :
    (1 : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J :=
  isPrimeTo_one J

example {I K : FractionalIdeal A⁰ (FractionRing A)} {J : Ideal A}
    (hI : I.IsPrimeTo J) (hK : K.IsPrimeTo J) :
    (I * K).IsPrimeTo J :=
  hI.mul hK

example {u : (FractionalIdeal A⁰ (FractionRing A))ˣ} {J : Ideal A}
    (hu : (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J) :
    ((u⁻¹ : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
      FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J :=
  hu.inv_unit

example {u : (FractionalIdeal A⁰ (FractionRing A))ˣ} {J : Ideal A} :
    u ∈ unitsPrimeTo J ↔
      (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J :=
  mem_unitsPrimeTo_iff

example {I : FractionalIdeal A⁰ (FractionRing A)} {J K : Ideal A}
    (hI : I.IsPrimeTo J) (hJK : J ≤ K) :
    I.IsPrimeTo K :=
  hI.mono hJK

example {J K : Ideal A} (hJK : J ≤ K) :
    unitsPrimeTo (A := A) J ≤ unitsPrimeTo K :=
  unitsPrimeTo_mono hJK

example : unitsPrimeTo (⊤ : Ideal ℤ) = ⊤ :=
  unitsPrimeTo_top

example (u : (FractionalIdeal ℤ⁰ (FractionRing ℤ))ˣ) :
    u ∈ unitsPrimeTo (⊤ : Ideal ℤ) := by
  rw [unitsPrimeTo_top]
  trivial

end FractionalIdeal
end
