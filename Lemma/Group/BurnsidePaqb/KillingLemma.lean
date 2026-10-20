import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb.KillingLemma
open BurnsidePaqb


/--
[character_eq_sum_roots](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma character_eq_sum_roots_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}
  {g : G} :
-- imply
  ρ.character g = (ρ g).charpoly.roots.sum := by
-- proof
  apply BurnsidePaqb.character_eq_sum_roots ρ g

/--
[charpoly_root_pow_orderOf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma charpoly_root_pow_orderOf_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}
  {g : G}
  {μ : ℂ}
-- given
  (hμ : μ ∈ (ρ g).charpoly.roots) :
-- imply
  μ ^ orderOf g = 1 := by
-- proof
  apply BurnsidePaqb.charpoly_root_pow_orderOf ρ g μ hμ

/--
[charpoly_root_norm_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma charpoly_root_norm_eq_one_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Finite G]
  {ρ : Representation ℂ G V}
  {g : G}
  {μ : ℂ}
-- given
  (hμ : μ ∈ (ρ g).charpoly.roots) :
-- imply
  ‖μ‖ = 1 := by
-- proof
  apply BurnsidePaqb.charpoly_root_norm_eq_one ρ g μ hμ

/--
[re_mul_conj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma re_mul_conj_eq
  [Group G] [Fintype G]
  {a b : ℂ} :
-- imply
  a.re * b.re + a.im * b.im = (a * starRingEnd ℂ b).re := by
-- proof
  apply BurnsidePaqb.re_mul_conj a b

/--
[norm_mul_conj_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma norm_mul_conj_eq_one_eq
  [Group G] [Fintype G]
  {a b : ℂ}
-- given
  (ha : ‖a‖ = 1)
  (hb : ‖b‖ = 1) :
-- imply
  ‖a * starRingEnd ℂ b‖ = 1 := by
-- proof
  apply BurnsidePaqb.norm_mul_conj_eq_one a b ha hb

/--
[eq_of_mul_conj_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma eq_of_mul_conj_eq_one_eq
  [Group G] [Fintype G]
  {a b : ℂ}
-- given
  (hb : ‖b‖ = 1)
  (h : a * starRingEnd ℂ b = 1) :
-- imply
  a = b := by
-- proof
  apply BurnsidePaqb.eq_of_mul_conj_eq_one a b hb h

/--
[re_lt_one_of_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma re_lt_one_of_ne_one_eq
  [Group G] [Fintype G]
  {w : ℂ}
-- given
  (hw : ‖w‖ = 1)
  (hne : w ≠ 1) :
-- imply
  w.re < 1 := by
-- proof
  apply BurnsidePaqb.re_lt_one_of_ne_one w hw hne

/--
[abs_sum_roots_of_unity_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma abs_sum_roots_of_unity_lt_eq
  [Group G] [Fintype G]
  {n : ℕ}
  {μ : Fin n → ℂ}
-- given
  (hmod : ∀ i, ‖μ i‖ = 1)
  (hne : ∃ i j, μ i ≠ μ j) :
-- imply
  ‖∑ i, μ i‖ < n := by
-- proof
  apply BurnsidePaqb.abs_sum_roots_of_unity_lt μ hmod hne

/--
[character_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma character_isIntegral_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Finite G]
  {ρ : Representation ℂ G V}
  {g : G} :
-- imply
  IsIntegral ℤ (ρ.character g) := by
-- proof
  apply BurnsidePaqb.character_isIntegral ρ g

/--
[charDivDeg_isIntegral_of_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma charDivDeg_isIntegral_of_coprime_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {g : G}
-- given
  (hcop : Nat.Coprime (conjClass g).card (Module.finrank ℂ V)) :
-- imply
  IsIntegral ℤ (ρ.character g / ρ.character 1) := by
-- proof
  apply BurnsidePaqb.charDivDeg_isIntegral_of_coprime ρ g hcop

/--
[abs_add_two_ne_unit_lt_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma abs_add_two_ne_unit_lt_two_eq
  [Group G] [Fintype G]
  {a b : ℂ}
-- given
  (ha : ‖a‖ = 1)
  (hb : ‖b‖ = 1)
  (hne : a ≠ b) :
-- imply
  ‖a + b‖ < 2 := by
-- proof
  apply BurnsidePaqb.abs_add_two_ne_unit_lt_two ha hb hne

/--
[abs_multiset_sum_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma abs_multiset_sum_lt_eq
  [Group G] [Fintype G]
  {s : Multiset ℂ}
-- given
  (hunit : ∀ μ ∈ s, ‖μ‖ = 1)
  (hne : ∃ a ∈ s, ∃ b ∈ s, a ≠ b) :
-- imply
  ‖s.sum‖ < s.card := by
-- proof
  apply BurnsidePaqb.abs_multiset_sum_lt s hunit hne

/--
[charpoly_roots_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma charpoly_roots_card_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}
  {g : G} :
-- imply
  (ρ g).charpoly.roots.card = Module.finrank ℂ V := by
-- proof
  apply BurnsidePaqb.charpoly_roots_card ρ g

/--
[char_roots_not_all_equal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma char_roots_not_all_equal_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [Finite G]
  {ρ : Representation ℂ G V}
  {g : G}
-- given
  (hlt : ‖ρ.character g‖ < Module.finrank ℂ V) :
-- imply
  ∃ a ∈ (ρ g).charpoly.roots, ∃ b ∈ (ρ g).charpoly.roots, a ≠ b := by
-- proof
  apply BurnsidePaqb.char_roots_not_all_equal ρ g hlt

/--
[char_mem_cycSubfield](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma char_mem_cycSubfield_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}
  {g : G}
-- given
  (hm : orderOf g ≠ 0) :
-- imply
  ρ.character g ∈ cycSubfield (orderOf g) := by
-- proof
  apply BurnsidePaqb.char_mem_cycSubfield ρ g hm

/--
[embedding_char_eq_conj_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma embedding_char_eq_conj_sum_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {m : ℕ}
  {ρ : Representation ℂ G V}
  {g : G}
  {σ : cycSubfield m →ₐ[ℚ] ℂ}
-- given
  (hm : m ≠ 0)
  (hmg : ∀ μ ∈ (ρ g).charpoly.roots, μ ^ m = 1)
  (hχ : ρ.character g ∈ cycSubfield m) :
-- imply
  σ ⟨ρ.character g, hχ⟩
    = (((ρ g).charpoly.roots.attach.map
    (fun x => σ (conjRootElem m hm ρ g hmg x))).sum) := by
-- proof
  apply BurnsidePaqb.embedding_char_eq_conj_sum m hm ρ g hmg hχ σ

/--
[char_eq_zero_of_coprime_of_norm_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma char_eq_zero_of_coprime_of_norm_lt_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {g : G}
-- given
  (hcop : Nat.Coprime (conjClass g).card (Module.finrank ℂ V))
  (hlt : ‖ρ.character g‖ < Module.finrank ℂ V) :
-- imply
  ρ.character g = 0 := by
-- proof
  apply BurnsidePaqb.char_eq_zero_of_coprime_of_norm_lt ρ g hcop hlt

/--
[burnside_coprime_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean)
-/
@[path]
private lemma burnside_coprime_vanish_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {g : G}
-- given
  (hcop : Nat.Coprime (conjClass g).card (Module.finrank ℂ V)) :
-- imply
  ‖ρ.character g‖ = Module.finrank ℂ V ∨ ρ.character g = 0 := by
-- proof
  apply BurnsidePaqb.burnside_coprime_vanish ρ g hcop


-- created on 2026-10-20
