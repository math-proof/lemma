import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.Ch22ConductorDef
open RayClassField
open scoped NumberField


namespace RayClassField

/--
[conductorModulus_witness_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22ConductorDef.lean)
-/
@[path]
lemma conductorModulus_witness_spec
  {K : Type u}
  [Field K]
  [NumberField K]
  {p : CongruenceSubgroupPair K} :
-- imply
  p.IsEquiv (corollary_22_7_existence p).choose ∧ ∀ q : CongruenceSubgroupPair K, p.IsEquiv q → (conductorModulus p).dvd q.modulus :=
-- proof
  (corollary_22_7_existence p).choose_spec

end RayClassField

namespace RayClassField

/--
[conductorModulus_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22ConductorDef.lean)
-/
@[path]
lemma conductorModulus_dvd
  {K : Type u}
  [Field K]
  [NumberField K]
  {p : CongruenceSubgroupPair K} :
-- imply
  (conductorModulus p).dvd p.modulus :=
-- proof
  (conductorModulus_witness_spec p).2 p (CongruenceSubgroupPair.isEquiv_refl p)

end RayClassField

namespace RayClassField

/--
[conductorModulus_dvd_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22ConductorDef.lean)
-/
@[path]
lemma conductorModulus_dvd_of_equiv
  {K : Type u}
  [Field K]
  [NumberField K]
  {p p' : CongruenceSubgroupPair K}
-- given
  (h : p.IsEquiv p') :
-- imply
  (conductorModulus p).dvd p'.modulus :=
-- proof
  (conductorModulus_witness_spec p).2 p' h

end RayClassField

namespace RayClassField

/--
[conductorModulus_eq_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22ConductorDef.lean)
-/
@[path]
lemma conductorModulus_eq_of_equiv
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ p₂ : CongruenceSubgroupPair K}
-- given
  (h : p₁.IsEquiv p₂) :
-- imply
  conductorModulus p₁ = conductorModulus p₂ := by
-- proof
  have h₁₂ : (conductorModulus p₁).dvd (conductorModulus p₂) := by
    have hp₂₀ := (conductorModulus_witness_spec p₂).1
    have hp₁_witness₂ : p₁.IsEquiv (corollary_22_7_existence p₂).choose :=
      h.trans' hp₂₀
    exact (conductorModulus_witness_spec p₁).2 _ hp₁_witness₂
  have h₂₁ : (conductorModulus p₂).dvd (conductorModulus p₁) := by
    have hp₁₀ := (conductorModulus_witness_spec p₁).1
    have hp₂_witness₁ : p₂.IsEquiv (corollary_22_7_existence p₁).choose :=
      h.symm'.trans' hp₁₀
    exact (conductorModulus_witness_spec p₂).2 _ hp₂_witness₁
  exact Modulus.dvd_antisymm' h₁₂ h₂₁

end RayClassField

namespace RayClassField

/--
[conductorModulus_exists_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22ConductorDef.lean)
-/
@[path]
lemma conductorModulus_exists_equiv
  {K : Type u}
  [Field K]
  [NumberField K]
  {p : CongruenceSubgroupPair K} :
-- imply
  ∃ p' : CongruenceSubgroupPair K, p'.modulus = conductorModulus p ∧ p.IsEquiv p' :=
-- proof
  ⟨(corollary_22_7_existence p).choose, rfl, (conductorModulus_witness_spec p).1⟩

end RayClassField

namespace RayClassField

/--
[CongruenceSubgroupPair.conductor_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22ConductorDef.lean)
-/
@[path]
lemma CongruenceSubgroupPair.conductor_dvd
  {K : Type u}
  [Field K]
  [NumberField K]
  {p : CongruenceSubgroupPair K} :
-- imply
  p.conductor.dvd p.modulus :=
-- proof
  conductorModulus_dvd p

end RayClassField

namespace RayClassField

/--
[CongruenceSubgroupPair.conductor_dvd_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22ConductorDef.lean)
-/
@[path]
lemma CongruenceSubgroupPair.conductor_dvd_of_equiv
  {K : Type u}
  [Field K]
  [NumberField K]
  {p p' : CongruenceSubgroupPair K}
-- given
  (h : p.IsEquiv p') :
-- imply
  p.conductor.dvd p'.modulus :=
-- proof
  conductorModulus_dvd_of_equiv p p' h

end RayClassField

namespace RayClassField

/--
[CongruenceSubgroupPair.conductor_eq_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22ConductorDef.lean)
-/
@[path]
lemma CongruenceSubgroupPair.conductor_eq_of_equiv
  {K : Type u}
  [Field K]
  [NumberField K]
  {p₁ p₂ : CongruenceSubgroupPair K}
-- given
  (h : p₁.IsEquiv p₂) :
-- imply
  p₁.conductor = p₂.conductor :=
-- proof
  conductorModulus_eq_of_equiv p₁ p₂ h

end RayClassField


-- created on 2026-10-23
