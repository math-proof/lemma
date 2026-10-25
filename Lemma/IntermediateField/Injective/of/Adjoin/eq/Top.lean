import Mathlib
import sympy.Basic
import Lemma.Scheme.IsCurveOver
import Lemma.Int.P2MUtil

open AlgebraicCurve KaehlerDifferential

/--
[AlgebraicCurve_kaehlerDifferential_map_injective_of_constantFieldExtension](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_kaehlerDifferential_map_injective_of_constantFieldExtension.lean)
-/

noncomputable def kerField {E FE : Type*} [Field E] [Field FE] [Algebra E FE]
  (d : Derivation E FE Ω[FE⁄E]) : IntermediateField E FE where
  carrier := {z | d z = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  one_mem' := by simp only [Set.mem_ofPred_eq]; exact Derivation.map_one_eq_zero _
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]
  zero_mem' := by simp only [Set.mem_ofPred_eq]; exact map_zero _
  algebraMap_mem' r := by simp only [Set.mem_ofPred_eq]; exact Derivation.map_algebraMap _ _
  inv_mem' a ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [Derivation.leibniz_inv, ha, smul_zero]

private lemma  mem_kerField {E FE : Type*} [Field E] [Field FE] [Algebra E FE]
  (d : Derivation E FE Ω[FE⁄E]) (z : FE) : z ∈ kerField d ↔ d z = 0 := Iff.rfl


@[path]
private lemma main
  [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE] [PerfectField K] [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver E FE]
-- given
  (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
-- imply
  Function.Injective (KaehlerDifferential.map K E F FE) := by
  classical
    have hex : ∃ g : F, D E FE (algebraMap F FE g) ≠ 0 := by
-- proof
      by_contra hall
      push Not at hall
      have hle : (⊤ : IntermediateField E FE) ≤ kerField (D E FE) := by
        rw [← hgen, IntermediateField.adjoin_le_iff]
        rintro _ ⟨g, rfl⟩
        exact hall g
      have hD : ∀ z : FE, D E FE z = 0 := fun z => (mem_kerField _ z).1 (hle IntermediateField.mem_top)
      have htop : (⊤ : Submodule FE Ω[FE⁄E]) = ⊥ := by
        rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
        rintro _ ⟨z, rfl⟩
        exact hD z
      obtain ⟨a, b, hab⟩ := (IsCurveOver.instNontrivialKaehler (K := E) (F := FE)).exists_pair_ne
      have ha : a ∈ (⊤ : Submodule FE Ω[FE⁄E]) := trivial
      have hb : b ∈ (⊤ : Submodule FE Ω[FE⁄E]) := trivial
      rw [htop, Submodule.mem_bot] at ha hb
      exact hab (ha.trans hb.symm)
    obtain ⟨g, hg⟩ := hex
    set m := KaehlerDifferential.map K E F FE with hm
    have hmg : m (D K F g) ≠ 0 := by
      rw [hm, KaehlerDifferential.map_D]; exact hg
    have hg0 : D K F g ≠ 0 := fun h => hmg (by rw [h, map_zero])
    rw [injective_iff_map_eq_zero]
    intro ω hω
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (D K F g) hg0).1 IsCurveOver.finrank_kaehler ω
    rw [map_smul, algebra_compatible_smul FE c, smul_eq_zero] at hω
    rcases hω with hc | h0
    ·
      rw [(algebraMap F FE).injective.eq_iff' (map_zero _)] at hc
      rw [hc, zero_smul]
    · exact (hmg h0).elim


-- created on 2026-10-23
