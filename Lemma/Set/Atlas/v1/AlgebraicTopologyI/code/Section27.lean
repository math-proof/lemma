import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section27
open CategoryTheory AlgebraicTopology Limits UniversalCoefficientTheorem


namespace UniversalCoefficientTheorem

/--
[splitting_from_biprod_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section27.lean)
-/
@[path]
lemma splitting_from_biprod_iso
  [Category C]
  [Preadditive C]
  [HasZeroObject C]
  {A B D : C}
  [HasBinaryBiproduct A D]
  {φ : A ⊞ D ≅ B} :
-- imply
  ∃ (S : ShortComplex C), S.X₁ = A ∧ S.X₂ = B ∧ S.X₃ = D ∧ S.ShortExact ∧ Nonempty S.Splitting := by
-- proof
  let S : ShortComplex C :=
    ShortComplex.mk (biprod.inl ≫ φ.hom) (φ.inv ≫ biprod.snd) (by simp)
  have split : S.Splitting := {
    r := φ.inv ≫ biprod.fst
    s := biprod.inr ≫ φ.hom
    f_r := by
      show (biprod.inl ≫ φ.hom) ≫ (φ.inv ≫ biprod.fst) = 𝟙 A
      simp [Category.assoc]
    s_g := by
      show (biprod.inr ≫ φ.hom) ≫ (φ.inv ≫ biprod.snd) = 𝟙 D
      simp [Category.assoc]
    id := by
      show (φ.inv ≫ biprod.fst) ≫ (biprod.inl ≫ φ.hom) +
        (φ.inv ≫ biprod.snd) ≫ (biprod.inr ≫ φ.hom) = 𝟙 B
      simp only [Category.assoc]
      rw [← Preadditive.comp_add, ← Category.assoc biprod.fst,
        ← Category.assoc biprod.snd, ← Preadditive.add_comp,
        biprod.total, Category.id_comp, Iso.inv_hom_id]
  }
  exact ⟨S, rfl, rfl, rfl, split.shortExact, ⟨split⟩⟩

end UniversalCoefficientTheorem


-- created on 2026-10-23
