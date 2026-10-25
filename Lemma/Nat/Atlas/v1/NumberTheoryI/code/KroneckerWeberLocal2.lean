import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.KroneckerWeberLocal2.Part2
open KroneckerWeberLocal2


namespace KroneckerWeberLocal2

/--
[Z2Z4_index2_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean)
-/
@[path]
lemma Z2Z4_index2_count
-- imply
  Nat.card {H : Subgroup (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) // H.index = 2} = 15 :=
-- proof
  GroupCounts.Z2Z4_index2_count

end KroneckerWeberLocal2

namespace KroneckerWeberLocal2

/--
[Z4Z3_cyclic_quartic_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean)
-/
@[path]
lemma Z4Z3_cyclic_quartic_count
-- imply
  Nat.card {H : Subgroup (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) // H.index = 4 ∧ IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)} = 28 :=
-- proof
  GroupCounts.Z4Z3_cyclic_quartic_count

end KroneckerWeberLocal2

namespace KroneckerWeberLocal2

/--
[galois_quotient_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean)
-/
@[path]
lemma galois_quotient_extension
  {F : Type u₁} [Field F]
  {L : Type u₂} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {Q : Type u₃} [Group Q] [Fintype Q]
  {φ : (L ≃ₐ[F] L) →* Q}
-- given
  (hφ : Function.Surjective φ) :
-- imply
  ∃ (E : Type u₂) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E), Nonempty ((E ≃ₐ[F] E) ≃* Q) := by
-- proof
  let H := φ.ker
  let E := IntermediateField.fixedField H
  haveI : Subgroup.Normal H := φ.normal_ker
  haveI : IsGalois F E := IsGalois.of_fixedField_normal_subgroup H
  have iso1 : (L ≃ₐ[F] L) ⧸ H ≃* (↥E ≃ₐ[F] ↥E) := IsGalois.normalAutEquivQuotient H
  have iso2 : (L ≃ₐ[F] L) ⧸ H ≃* Q := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  exact ⟨↥E, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨iso1.symm.trans iso2⟩⟩

end KroneckerWeberLocal2

namespace KroneckerWeberLocal2

/--
[surjective_toMultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean)
-/
@[path]
lemma surjective_toMultiplicative
  [AddCommMonoid A]
  [AddCommMonoid B]
  {f : A →+ B}
-- given
  (hf : Function.Surjective f) :
-- imply
  Function.Surjective (AddMonoidHom.toMultiplicative f) := by
-- proof
  intro b
  obtain ⟨a, ha⟩ := hf (Multiplicative.toAdd b)
  exact ⟨Multiplicative.ofAdd a, by simp [AddMonoidHom.toMultiplicative, ha]⟩

end KroneckerWeberLocal2

namespace KroneckerWeberLocal2

/--
[addMonoidHom_prodMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean)
-/
@[path]
lemma addMonoidHom_prodMap_surjective
  [AddZeroClass M]
  [AddZeroClass N]
  [AddZeroClass M']
  [AddZeroClass N']
  {f : M →+ M'}
  {g : N →+ N'}
-- given
  (hf : Function.Surjective f)
  (hg : Function.Surjective g) :
-- imply
  Function.Surjective (AddMonoidHom.prodMap f g) := by
-- proof
  intro ⟨m', n'⟩
  obtain ⟨m, hm⟩ := hf m'
  obtain ⟨n, hn⟩ := hg n'
  exact ⟨(m, n), Prod.ext (by simp [hm]) (by simp [hn])⟩
end KroneckerWeberLocal2


/--
[index_map_mulEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean)
-/
@[path]
private lemma index_map_mulEquiv_eq
  [Group G]
  [Group G']
  {φ : G ≃* G'}
  {H : Subgroup G} :
-- imply
  (H.map φ.toMonoidHom).index = H.index := by
-- proof
  apply KroneckerWeberLocal2.index_map_mulEquiv φ H

/--
[index_subgroups_card_eq_of_mulEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean)
-/
@[path]
private lemma index_subgroups_card_eq_of_mulEquiv_eq
  [Group G]
  [Group G']
  {φ : G ≃* G'}
  {n : ℕ} :
-- imply
  Nat.card {H : Subgroup G // H.index = n} = Nat.card {H : Subgroup G' // H.index = n} := by
-- proof
  apply KroneckerWeberLocal2.index_subgroups_card_eq_of_mulEquiv φ n

/--
[Z4Z3_cyclic_quartic_count_with_normal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean)
-/
@[path]
private lemma Z4Z3_cyclic_quartic_count_with_normal_eq :
-- imply
  Nat.card {H : Subgroup (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) // H.index = 4 ∧ ∃ (_ : H.Normal), IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)} = 28 := by
-- proof
  apply KroneckerWeberLocal2.Z4Z3_cyclic_quartic_count_with_normal

/--
[cyclic_normal_index_subgroups_card_eq_of_mulEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean)
-/
@[path]
private lemma cyclic_normal_index_subgroups_card_eq_of_mulEquiv_eq
  {G G' : Type}
  [Group G]
  [Group G']
  {φ : G ≃* G'}
  {n : ℕ} :
-- imply
  Nat.card {H : Subgroup G // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G ⧸ H)} = Nat.card {H : Subgroup G' // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G' ⧸ H)} := by
-- proof
  apply KroneckerWeberLocal2.cyclic_normal_index_subgroups_card_eq_of_mulEquiv φ n


-- created on 2026-10-23
