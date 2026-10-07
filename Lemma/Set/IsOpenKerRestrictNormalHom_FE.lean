import Mathlib
import sympy.Basic


/--
[AlgEquiv_isOpen_ker_restrictNormalHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgEquiv_isOpen_ker_restrictNormalHom.lean)
-/
@[main]
private lemma main
  [Field E]
  {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Normal K E] [FiniteDimensional K E] :
-- imply
  IsOpen ((AlgEquiv.restrictNormalHom (F :=
-- proof
  K) (K₁ := L) E).ker : Set (L ≃ₐ[K] L)) := by
   let ι : E →ₐ[K] L := IsScalarTower.toAlgHom K E L
   let L' : IntermediateField K L := ι.fieldRange
   have : FiniteDimensional K L' := Module.Finite.equiv
     (((IntermediateField.topEquiv (F := K) (E := E)).symm.trans (IntermediateField.equivMap ⊤ ι)).trans
       (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map ι).symm)).toLinearEquiv
   apply Subgroup.isOpen_mono (H₁ := L'.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen L')
   intro σ hσ
   rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
   rw [MonoidHom.mem_ker]
   apply AlgEquiv.ext
   intro y
   apply (algebraMap E L).injective
   have hc := AlgEquiv.restrictNormal_commutes σ E y
   change algebraMap E L ((σ.restrictNormal E) y) = algebraMap E L ((1 : E ≃ₐ[K] E) y)
   rw [AlgEquiv.one_apply, hc]
   exact hσ _ (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)


-- created on 2026-10-05
