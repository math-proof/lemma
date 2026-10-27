import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_fppf_exists_section_of_map_eq_unit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit.lean)
-/
@[path]
private lemma main
  {E : CategoryTheory.Sheaf Scheme.fppfTopology (AddCommGrpCat : Type 2)}
  (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology (AddCommGrpCat : Type 2)).obj (.of ((ULift ℤ : Type 1))))
  (e : ToType (E.obj.obj (op (Spec (.of ℤ)))))
  (he : g.hom.app (op (Spec (.of ℤ))) e = (CategoryTheory.constantSheafAdj Scheme.fppfTopology (AddCommGrpCat : Type 2) AlgebraicGeometry.specZIsTerminal).unit.app (.of ((ULift ℤ : Type 1))) (ULift.up 1)) :
  -- imply
  ∃ s : (CategoryTheory.constantSheaf Scheme.fppfTopology (AddCommGrpCat : Type 2)).obj (.of ((ULift ℤ : Type 1))) ⟶ E, s ≫ g = 𝟙 _ := by
  -- proof
  let adj := CategoryTheory.constantSheafAdj Scheme.fppfTopology (AddCommGrpCat : Type 2) AlgebraicGeometry.specZIsTerminal
  let φ : (AddCommGrpCat.of ((ULift ℤ : Type 1))) ⟶ E.obj.obj (op (Spec (.of ℤ))) :=
    AddCommGrpCat.ofHom (((zmultiplesHom (E.obj.obj (op (Spec (.of ℤ))))) e).comp AddEquiv.ulift.toAddMonoidHom)
  have hφ : φ (ULift.up 1) = e := by
    change (AddEquiv.ulift (ULift.up (1 : ℤ))) • e = e
    apply one_zsmul
  refine ⟨(adj.homEquiv _ E).symm φ, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, Adjunction.homEquiv_id]
  ext x
  obtain ⟨n⟩ := x
  have hx : (ULift.up n : (ULift ℤ : Type 1)) = n • ULift.up 1 := by
    ext
    simp
  rw [hx, map_zsmul, map_zsmul]
  congr 1
  change g.hom.app (op (Spec (.of ℤ))) (φ (ULift.up 1)) = adj.unit.app _ (ULift.up 1)
  rw [hφ]
  apply he


-- created on 2026-10-20
