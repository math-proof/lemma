import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.DirichletCharacters
open DirichletCharacter in Filter Topology CharacterGroup
open Filter Topology


namespace CharacterGroup

/--
[prop_18_33_mulEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean)
-/
@[path]
lemma prop_18_33_mulEquiv
  [CommGroup G]
  [Fintype G] :
-- imply
  Nonempty (CharacterGroup G ≃* G) :=
-- proof
  CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ

end CharacterGroup

namespace CharacterGroup

/--
[cor_18_34](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean)
-/
@[path]
lemma cor_18_34
  [CommGroup G]
  [Fintype G]
  {g : G} :
-- imply
  g = 1 ↔ ∀ χ : CharacterGroup G, χ g = 1 := by
-- proof
  constructor
  · rintro rfl; intro χ; exact map_one χ
  · intro h
    exact (CommGroup.forall_apply_eq_apply_iff G (M := ℂ) (g := g) (g' := 1)).mp
      fun φ => by simp [h φ]

end CharacterGroup

namespace CharacterGroup

/--
[cor_18_34_part2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean)
-/
@[path]
lemma cor_18_34_part2
  [CommGroup G]
  [Fintype G]
  {χ : CharacterGroup G} :
-- imply
  χ = 1 ↔ ∀ g : G, χ g = 1 := by
-- proof
  constructor
  · intro h g
    simp [h]
  · intro h
    ext g
    simp [h g]

end CharacterGroup

namespace CharacterGroup

/--
[characters_separate_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean)
-/
@[path]
lemma characters_separate_points
  [CommGroup G]
  [Fintype G] :
-- imply
  (∀ g : G, g = 1 ↔ ∀ χ : CharacterGroup G, χ g = 1) ∧ (∀ χ : CharacterGroup G, χ = 1 ↔ ∀ g : G, χ g = 1) :=
-- proof
  ⟨cor_18_34, cor_18_34_part2⟩

end CharacterGroup

namespace DirichletCharacter

/--
[thm_18_13_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean)
-/
@[path]
lemma thm_18_13_existence
  [CommMonoidWithZero R]
  {n : ℕ}
  {χ : DirichletCharacter R n} :
-- imply
  χ.primitiveCharacter.IsPrimitive ∧ changeLevel χ.conductor_dvd_level χ.primitiveCharacter = χ :=
-- proof
  ⟨χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩

end DirichletCharacter

namespace DirichletCharacter

/--
[thm_18_13_unique_level](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean)
-/
@[path]
lemma thm_18_13_unique_level
  [CommMonoidWithZero R]
  {n : ℕ}
  {χ : DirichletCharacter R n}
  {m : ℕ}
  {χ' : DirichletCharacter R m}
-- given
  (hn : n ≠ 0)
  (hm : m ∣ n)
  (hind : changeLevel hm χ' = χ)
  (hprim : χ'.IsPrimitive) :
-- imply
  m = χ.conductor := by
-- proof
  have hm_cond : m ∈ χ.conductorSet := ⟨hm, χ', hind.symm⟩
  have hc_dvd_m : χ.conductor ∣ m := conductor_dvd_of_mem_conductorSet χ hn hm_cond
  have hm_ne : m ≠ 0 := fun h => hn (Nat.eq_zero_of_zero_dvd (h ▸ hm))
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero m := ⟨hm_ne⟩
  have key : χ' = changeLevel hc_dvd_m χ.primitiveCharacter := by
    apply changeLevel_injective hm
    rw [hind, ← changeLevel_trans χ.primitiveCharacter hc_dvd_m hm,
      changeLevel_primitiveCharacter]
  have hft : χ'.FactorsThrough χ.conductor := ⟨hc_dvd_m, χ.primitiveCharacter, key⟩
  have h_cond_le : χ'.conductor ≤ χ.conductor := Nat.sInf_le hft
  rw [(isPrimitive_def χ').mp hprim] at h_cond_le
  exact ((Nat.le_of_dvd (Nat.pos_of_ne_zero hm_ne) hc_dvd_m).antisymm h_cond_le).symm

end DirichletCharacter

namespace DirichletCharacter

/--
[thm_18_13_unique_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean)
-/
@[path]
lemma thm_18_13_unique_char
  [CommMonoidWithZero R]
  {n : ℕ}
  {χ : DirichletCharacter R n}
  {χ' : DirichletCharacter R χ.conductor}
-- given
  (hn : n ≠ 0)
  (hm : χ.conductor ∣ n)
  (hind : changeLevel hm χ' = χ)
  (hprim : χ'.IsPrimitive) :
-- imply
  χ' = χ.primitiveCharacter := by
-- proof
  haveI : NeZero n := ⟨hn⟩
  apply changeLevel_injective hm
  rw [hind, changeLevel_primitiveCharacter]

end DirichletCharacter

namespace DirichletCharacter

/--
[thm_18_13](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean)
-/
@[path]
lemma thm_18_13
  [CommMonoidWithZero R]
  {n : ℕ}
  {χ : DirichletCharacter R n}
-- given
  (hn : n ≠ 0) :
-- imply
  (χ.primitiveCharacter.IsPrimitive ∧ changeLevel χ.conductor_dvd_level χ.primitiveCharacter = χ) ∧ (∀ {m : ℕ} (hm : m ∣ n) (χ' : DirichletCharacter R m), changeLevel hm χ' = χ → χ'.IsPrimitive → ∃ (heq : m = χ.conductor), heq ▸ χ' = χ.primitiveCharacter) := by
-- proof
  refine ⟨thm_18_13_existence χ, ?_⟩
  intro m hm χ' hind hprim
  have heq : m = χ.conductor := thm_18_13_unique_level χ hn hm χ' hind hprim
  exact ⟨heq, by subst heq; exact thm_18_13_unique_char χ hn hm χ' hind hprim⟩
end DirichletCharacter
open Filter Topology



-- created on 2026-10-23
