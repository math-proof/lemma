/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ArakelovDivisor.lean -/


import Def.NumberTheory.NumberField.ArakelovDivisor.Part3
import Lemma.Nat.NumberField.ArakelovDivisor
open NumberField
open scoped nonZeroDivisors NumberField

/-!
# Tests for Arakelov divisors of a number field
-/


namespace MathlibExtTest.NumberTheory.ArakelovDivisor

variable {K : Type*} [Field K] [NumberField K]

/-- The identity Arakelov divisor has size one. -/
example : ArakelovDivisor.sizeHom K 1 = 1 := map_one _

/-- The size homomorphism is multiplicative. -/
example (D E : ArakelovDivisor K) :
    ArakelovDivisor.sizeHom K (D * E) =
      ArakelovDivisor.sizeHom K D * ArakelovDivisor.sizeHom K E :=
  map_mul _ _ _

/-- The size homomorphism is the quotient of the archimedean and ideal factors. -/
example (D : ArakelovDivisor K) :
    ArakelovDivisor.sizeHom K D =
      ArakelovDivisor.archHom K D / ArakelovDivisor.idealHom K D :=
  rfl

/-- The archimedean factor is multiplicative. -/
example (D E : ArakelovDivisor K) :
    ArakelovDivisor.archHom K (D * E) =
      ArakelovDivisor.archHom K D * ArakelovDivisor.archHom K E :=
  map_mul _ _ _

/-- The ideal norm is multiplicative. -/
example (D E : ArakelovDivisor K) :
    ArakelovDivisor.idealHom K (D * E) =
      ArakelovDivisor.idealHom K D * ArakelovDivisor.idealHom K E :=
  map_mul _ _ _

/-- The size of a principal divisor is one. -/
example (x : Kˣ) : ArakelovDivisor.sizeHom K (principalHom K x) = 1 :=
  size_principal K x

/-- The principal subgroup is contained in the degree-zero subgroup. -/
example : principalSubgroup K ≤ degreeZero K := principalSubgroup_le_degreeZero K

/-- Every principal divisor lies in the degree-zero subgroup. -/
example (x : Kˣ) : principalHom K x ∈ degreeZero K := by
  rw [degreeZero, MonoidHom.mem_ker]
  exact size_principal K x

/-- Smoke case over `ℚ`: there is a unique infinite place, it is real, and its
multiplicity is one. -/
example : Rat.infinitePlace.mult = 1 :=
  InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace

/-- Smoke case over `ℚ`: the size of a concrete principal divisor is one. -/
example : ArakelovDivisor.sizeHom ℚ
    (principalHom ℚ (Units.mk0 (2 : ℚ) (by norm_num))) = 1 :=
  size_principal ℚ _

/-- Smoke case over `ℚ`: the identity divisor has size one. -/
example : ArakelovDivisor.sizeHom ℚ 1 = 1 := map_one _

/-- Membership in a section set is ideal membership plus archimedean bounds. -/
example (D : ArakelovDivisor K) (x : K) :
    x ∈ D.sectionSet ↔
      x ∈ (D.1 : FractionalIdeal (𝓞 K)⁰ K) ∧
        ∀ w : InfinitePlace K, w x ≤ (D.2 w : ℝ) :=
  ArakelovDivisor.mem_sectionSet K D x

/-- Zero lies in the section set of the identity divisor. -/
example : (0 : K) ∈ (1 : ArakelovDivisor K).sectionSet := by
  rw [ArakelovDivisor.mem_sectionSet, Prod.fst_one, Units.val_one]
  refine ⟨FractionalIdeal.zero_mem _, fun w => ?_⟩
  rw [Prod.snd_one, Pi.one_apply, Positive.val_one, map_zero]
  exact zero_le_one

/-- Smoke case over `ℚ`: one lies in the section set of the identity divisor. -/
example : (1 : ℚ) ∈ (1 : ArakelovDivisor ℚ).sectionSet := by
  rw [ArakelovDivisor.mem_sectionSet, Prod.fst_one, Units.val_one]
  refine ⟨FractionalIdeal.one_mem_one _, fun w => ?_⟩
  rw [Prod.snd_one, Pi.one_apply, Positive.val_one, map_one]

/-- Every section set is finite. -/
example (D : ArakelovDivisor K) : D.sectionSet.Finite :=
  ArakelovDivisor.sectionSet_finite K D

/-- Every section set carries a finite-type structure. -/
noncomputable example (D : ArakelovDivisor K) : Fintype D.sectionSet :=
  (ArakelovDivisor.sectionSet_finite K D).fintype

/-- Smoke case over `ℚ`: the section set of the identity divisor is finite. -/
example : (1 : ArakelovDivisor ℚ).sectionSet.Finite :=
  ArakelovDivisor.sectionSet_finite ℚ 1

/-- Smoke case over `ℚ`: the section set of the identity divisor is a finite type. -/
noncomputable example : Fintype (1 : ArakelovDivisor ℚ).sectionSet :=
  (ArakelovDivisor.sectionSet_finite ℚ 1).fintype

end MathlibExtTest.NumberTheory.ArakelovDivisor
