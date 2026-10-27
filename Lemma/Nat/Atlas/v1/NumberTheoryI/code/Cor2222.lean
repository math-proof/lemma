import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.Cor2222
open NumberField RayClassField GlobalCFT CosetDensity


namespace CosetDensity

/--
[dirichletDensity_coprime_primes_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2222.lean)
-/
@[path]
lemma dirichletDensity_coprime_primes_eq_one
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
-- given
  (_h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
-- imply
  DirichletDensity K {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True} = some 1 :=
-- proof
GlobalCFT.dirichletDensity_coprime_primes_eq_one K 𝔪 𝒞 _h_cong

end CosetDensity

namespace CosetDensity

/--
[dirichletDensity_coset_partition_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2222.lean)
-/
@[path]
lemma dirichletDensity_coset_partition_sum
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {n : ℕ}
  {reps : Fin n → FracIdealsCoprime K 𝔪}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
  (hn : 𝒞.index = n)
  (hn_pos : 0 < n)
  (h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i))) :
-- imply
  (DirichletDensity K {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True}).getD 0 = ∑ i : Fin n, dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) :=
-- proof
GlobalCFT.dirichletDensity_coset_partition_sum K 𝔪 𝒞 h_cong n hn hn_pos reps h_reps

end CosetDensity

namespace CosetDensity

/--
[density_cosets_sum_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2222.lean)
-/
@[path]
lemma density_cosets_sum_one
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {n : ℕ}
  {reps : Fin n → FracIdealsCoprime K 𝔪}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
  (hn : 𝒞.index = n)
  (hn_pos : 0 < n)
  (h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i))) :
-- imply
  ∑ i : Fin n, dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 1 := by
-- proof
  have h_sum := dirichletDensity_coset_partition_sum K 𝔪 𝒞 h_cong n hn hn_pos reps h_reps
  have h_one := dirichletDensity_coprime_primes_eq_one K 𝔪 𝒞 h_cong
  rw [h_one] at h_sum
  simp [Option.getD] at h_sum
  linarith

end CosetDensity

namespace CosetDensity

/--
[corollary_22_22](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2222.lean)
-/
@[path]
lemma corollary_22_22
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {n : ℕ}
  {reps : Fin n → FracIdealsCoprime K 𝔪}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
  (hn : 𝒞.index = n)
  (hn_pos : 0 < n)
  (h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i))) :
-- imply
  AllLValuesNonzero K 𝔪 𝒞 ∧ ∀ (I : FracIdealsCoprime K 𝔪), dirichletDensityCoset K 𝔪 𝒞 h_cong I = 1 / (n : ℚ) := by
-- proof
  have h_sum := density_cosets_sum_one K 𝔪 𝒞 h_cong n hn hn_pos reps h_reps
  have h_each : ∀ i : Fin n,
    (AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 1 / (n : ℚ)) ∧
    (¬ AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 0) :=
    fun i => Prop2221.proposition_22_21 K 𝔪 𝒞 h_cong n hn hn_pos (reps i)
  have hL : AllLValuesNonzero K 𝔪 𝒞 := by
    by_contra hL
    have h_zero : ∀ i : Fin n,
      dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 0 :=
      fun i => (h_each i).2 hL
    simp only [h_zero, Finset.sum_const_zero] at h_sum
    exact one_ne_zero h_sum.symm
  exact ⟨hL, fun I => (Prop2221.proposition_22_21 K 𝔪 𝒞 h_cong n hn hn_pos I).1 hL⟩
end CosetDensity
namespace Cor2222
export CosetDensity (dirichletDensity_coprime_primes_eq_one dirichletDensity_coset_partition_sum
  density_cosets_sum_one corollary_22_22)
end Cor2222



-- created on 2026-10-23
