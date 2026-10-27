import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.CRTHelper
open RayClassField
open scoped NumberField
open IsDedekindDomain


namespace RayClassField

/--
[exists_ringOfIntegers_cong_mod_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CRTHelper.lean)
-/
@[path]
lemma exists_ringOfIntegers_cong_mod_primes
  {K : Type u}
  [Field K]
  [NumberField K]
  {s : Finset ι}
  {P : ι → FinitePlace K}
  {e : ι → ℕ}
  {x : s → 𝓞 K}
-- given
  (hP_inj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i ≠ P j) :
-- imply
  ∃ y : 𝓞 K, ∀ (i : ι) (hi : i ∈ s), y - x ⟨i, hi⟩ ∈ (P i).asIdeal ^ e i := by
-- proof
  have hprime : ∀ i ∈ s, Prime ((P i).asIdeal) := fun i _ => (P i).prime
  have hcoprime : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (P i).asIdeal ≠ (P j).asIdeal := by
    intro i hi j hj hij h
    exact absurd (HeightOneSpectrum.ext h) (hP_inj i hi j hj hij)
  exact IsDedekindDomain.exists_forall_sub_mem_ideal
    (fun i => (P i).asIdeal) e hprime hcoprime x

end RayClassField


-- created on 2026-10-23
