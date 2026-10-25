import Mathlib
import sympy.Basic
import Lemma.ModularCurve.ComponentGroup
import Lemma.ModularCurve.CharacterLatticePairings
import Lemma.Int.P2MUtil

open ModularCurve ModularCurve.CharacterLattice Finset

/--
[ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const.lean)
-/

def dzlE
  {S : Type*}
  [Fintype S]
  [DecidableEq S]
  (s₀ s : S) : characterLattice S :=
  ⟨Pi.single s 1 - Pi.single s₀ 1, single_sub_single_mem s s₀⟩

private lemma  coe_dzlE
  {S : Type*}
  [Fintype S]
  [DecidableEq S]
  (s₀ s : S) : (dzlE s₀ s : S → ℤ) = Pi.single s 1 - Pi.single s₀ 1 := rfl

private lemma  sum_smul_dzlE
  {S : Type*}
  [Fintype S]
  [DecidableEq S]
  (s₀ : S) (a : characterLattice S) :
  ∑ s, (a : S → ℤ) s • dzlE s₀ s = a := by
  have ha : ∑ s, (a : S → ℤ) s = 0 := mem_characterLattice.1 a.2
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  funext t
  simp only [Finset.sum_apply, Submodule.coe_smul_of_tower, coe_dzlE, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases ht : t = s₀ <;> simp [ht, ha]

private lemma  prod_zpow_single
  {S : Type*}
  [Fintype S]
  [DecidableEq S]
  {G : Type*}
  [CommGroup G]
  (s : S) (n : ℤ) (w : S → G) :
  ∏ t, w t ^ (Pi.single s n : S → ℤ) t = w s ^ n := by
  rw [Fintype.prod_eq_single s fun t ht => by rw [Pi.single_eq_of_ne ht, zpow_zero], Pi.single_eq_same]

private lemma  evalHom_dzlE
  {S : Type*}
  [Fintype S]
  [DecidableEq S]
  {G : Type*}
  [CommGroup G]
  (s₀ s : S) (w : S → G) : evalHom (dzlE s₀ s) w = w s * (w s₀)⁻¹ := by
  show zpowProd (Pi.single s (1 : ℤ) - Pi.single s₀ 1) w = _
  rw [sub_eq_add_neg, zpowProd_add, zpowProd_neg, zpowProd_def, zpowProd_def, prod_zpow_single,
    prod_zpow_single, zpow_one, zpow_one]
p2m_reactivate "P2MW.S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const.DZLTorusAux"

@[path]
private lemma main
  [Fintype S] [Nonempty S] [CommGroup G] :
-- imply
  (∀ χ : ModularCurve.characterLattice S →+ Additive G,
        ∃ w : S → G, ∀ a, Additive.toMul (χ a) = ModularCurve.CharacterLattice.evalHom a w) ∧
    (∀ w : S → G, (∀ a : ModularCurve.characterLattice S, ModularCurve.CharacterLattice.evalHom a w = 1) ↔
        ∃ c : G, w = fun _ => c) := by
-- proof
  classical
    obtain ⟨s₀⟩ := ‹Nonempty S›
    refine ⟨fun χ => ?_, fun w => ⟨fun h => ⟨w s₀, funext fun s => ?_⟩, ?_⟩⟩
    ·
      refine ⟨fun s => Additive.toMul (χ (dzlE s₀ s)), fun a => ?_⟩
      rw [evalHom_apply]
      conv_lhs => rw [← sum_smul_dzlE s₀ a, map_sum, toMul_sum]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [map_zsmul, toMul_zsmul]
    ·
      have hs := h (dzlE s₀ s)
      rw [evalHom_dzlE] at hs
      exact mul_inv_eq_one.mp hs
    ·
      rintro ⟨c, rfl⟩ a
      exact evalHom_const a c


-- created on 2026-10-23
