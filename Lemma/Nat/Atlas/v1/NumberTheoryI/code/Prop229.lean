import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.Prop229
open RayClassField
open scoped NumberField


namespace RayClassField

/--
[Modulus.ext_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop229.lean)
-/
@[path]
lemma Modulus.ext_iff
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K} :
-- imply
  𝔪 = 𝔫 ↔ ∀ v, 𝔪 v = 𝔫 v := by
-- proof
  constructor
  · rintro rfl; intro; rfl
  · intro h
    cases 𝔪; cases 𝔫
    congr 1
    funext v
    exact h v

end RayClassField

namespace RayClassField

/--
[Modulus.dvd_antisymm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop229.lean)
-/
@[path]
lemma Modulus.dvd_antisymm
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
-- given
  (h₁ : 𝔪.dvd 𝔫)
  (h₂ : 𝔫.dvd 𝔪) :
-- imply
  𝔪 = 𝔫 := by
-- proof
  rw [Modulus.ext_iff]
  intro v
  exact le_antisymm (h₁ v) (h₂ v)

end RayClassField

namespace RayClassField

/--
[proposition_22_9](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop229.lean)
-/
@[path]
lemma proposition_22_9
  {K : Type u}
  [Field K]
  [NumberField K]
  {p : CongruenceSubgroupPair K}
  {p₀ : CongruenceSubgroupPair K}
-- given
  (hmod : p₀.modulus = p.modulus)
  (hprim : p.IsPrimitive)
  (hle : p₀.toAmbientSubgroup ≤ p.toAmbientSubgroup) :
-- imply
  p₀.conductor = p.modulus := by
-- proof
  set 𝔠 := p₀.conductor with h𝔠_def
  have h𝔠_dvd_𝔪 : 𝔠.dvd p.modulus := by
    rwa [← hmod]
  obtain ⟨p₀', hp₀'_mod, hp₀'_equiv⟩ := conductorModulus_exists_equiv p₀
  have hp₀'_dvd : p₀'.modulus.dvd p₀.modulus := by
    rwa [hp₀'_mod]
  have hlem225_p₀ : FracIdealsCoprime_subgroup K p₀.modulus ⊓
    RayGroup.toAmbientSubgroup K p₀'.modulus ≤ p₀.toAmbientSubgroup :=
    lemma_22_5_necessity p₀ p₀' hp₀'_dvd hp₀'_equiv
  have hlem225_p : FracIdealsCoprime_subgroup K p.modulus ⊓
    RayGroup.toAmbientSubgroup K 𝔠 ≤ p.toAmbientSubgroup := by
    intro x hx
    apply hle
    have : x ∈ FracIdealsCoprime_subgroup K p₀.modulus ⊓
      RayGroup.toAmbientSubgroup K p₀'.modulus := by
      constructor
      · rw [hmod]; exact hx.1
      · rw [hp₀'_mod]; exact hx.2
    exact hlem225_p₀ this
  have hexists_equiv_𝔠 : ∃ p' : CongruenceSubgroupPair K,
    p'.modulus = 𝔠 ∧ p.IsEquiv p' := by
    rwa [lemma_22_5 p 𝔠 h𝔠_dvd_𝔪]
  have h𝔪_dvd_𝔠 : p.modulus.dvd 𝔠 := by
    obtain ⟨p', hp'_mod, hp'_equiv⟩ := hexists_equiv_𝔠
    have : p.conductor.dvd p'.modulus :=
      p.conductor_dvd_of_equiv p' hp'_equiv
    rw [hp'_mod] at this
    rwa [← hprim] at this
  exact Modulus.dvd_antisymm 𝔠 p.modulus h𝔠_dvd_𝔪 h𝔪_dvd_𝔠

end RayClassField


-- created on 2026-10-23
