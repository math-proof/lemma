import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.DedekindExtensions
open Module
open scoped nonZeroDivisors
open NumberField


/--
[dual_map_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean)
-/
@[path]
lemma dual_map_apply
  [CommRing A]
  [AddCommGroup M]
  [Module A M]
  {φ : M →ₗ[A] N}
  {g : Module.Dual A N}
  {m : M} :
-- imply
  φ.dualMap g m = g (φ m) :=
-- proof
  LinearMap.dualMap_apply φ g m
section DualDirectSum
variable (A : Type*) [CommRing A]
variable (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/--
[dualBasisProperty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean)
-/
@[path]
lemma dualBasisProperty
  [CommRing A]
  [AddCommGroup M]
  [Module A M]
  {n : ℕ}
  [DecidableEq ι]
  [Finite ι]
  {b : Basis ι A M}
  {i j : ι} :
-- imply
  b.dualBasis i (b j) = if j = i then 1 else 0 :=
-- proof
  b.dualBasis_apply_self i j
section PerfectPairingDualBasis
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
variable {ι : Type*} [DecidableEq ι] [Finite ι]

/--
[prime_chain_contracts_of_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean)
-/
@[path]
lemma prime_chain_contracts_of_integral
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [Algebra.IsIntegral A B]
  {q₀ q₁ : Ideal B}
  [q₀.IsPrime]
-- given
  (hlt : q₀ < q₁) :
-- imply
  q₀.comap (algebraMap A B) < q₁.comap (algebraMap A B) := by
-- proof
  obtain ⟨hle, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp hlt
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxJ, hxI⟩
    (Algebra.IsIntegral.isIntegral x)
section IntegralClosureDedekind

/--
[integral_closure_isDedekindDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean)
-/
@[path]
lemma integral_closure_isDedekindDomain
  {A : Type*}
  {K : Type*}
  [CommRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  {C : Type*}
  [CommRing C]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [Algebra C L]
  [IsIntegralClosure C A L]
  [Algebra A C]
  [IsScalarTower A C L]
  [FiniteDimensional K L]
  [IsDomain A]
  [Algebra.IsSeparable K L]
  [IsDomain C]
  [IsDedekindDomain A] :
-- imply
  IsDedekindDomain C :=
-- proof
  IsIntegralClosure.isDedekindDomain A K L C
end IntegralClosureDedekind
section RingOfIntegersDedekind
open NumberField

/--
[ringOfIntegers_isDedekindDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean)
-/
@[path]
lemma ringOfIntegers_isDedekindDomain
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  IsDedekindDomain (𝓞 K) :=
-- proof
  inferInstance
end RingOfIntegersDedekind
end

/--
[colonToA_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean)
-/
@[path]
private lemma colonToA_spec_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {M : Submodule A K}
  {x : colonSubmodule A K M}
  {m : M} :
-- imply
  algebraMap A K (colonToA A K M x m) = (x : K) * (m : K) := by
-- proof
  apply colonToA_spec A K M x m

/--
[dual_symmetric_relation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean)
-/
@[path]
private lemma dual_symmetric_relation_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {M : Submodule A K}
  {f : Module.Dual A M}
  {m₁ m₂ : M} :
-- imply
  (m₁ : K) * algebraMap A K (f m₂) = (m₂ : K) * algebraMap A K (f m₁) := by
-- proof
  apply dual_symmetric_relation A K M f m₁ m₂

/--
[dual_apply_via_element](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean)
-/
@[path]
private lemma dual_apply_via_element_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {M : Submodule A K}
  {f : Module.Dual A M}
  {m₀ : M}
  {m : M}
-- given
  (hm₀ : (m₀ : K) ≠ 0) :
-- imply
  algebraMap A K (f m₀) * (m₀ : K)⁻¹ * (m : K) = algebraMap A K (f m) := by
-- proof
  apply dual_apply_via_element A K M f m₀ hm₀ m

/--
[colonSubmodule_eq_coe_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean)
-/
@[path]
private lemma colonSubmodule_eq_coe_inv_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {M : FractionalIdeal A⁰ K}
-- given
  (hM : M ≠ 0) :
-- imply
  colonSubmodule A K (↑M : Submodule A K) = (↑(M⁻¹) : Submodule A K) := by
-- proof
  apply colonSubmodule_eq_coe_inv A K M hM


-- created on 2026-10-23
