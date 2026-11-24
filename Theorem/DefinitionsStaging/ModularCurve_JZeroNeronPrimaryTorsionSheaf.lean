module
public import Mathlib
public import Lemma.Definitions.Def_ModularCurve_JZeroNeronDataPrime
public import Lemma.Definitions.Def_ModularCurve_EisensteinIdeal
public import Structure.ModularCurve_FppfKummerInterface
public import Lemma.Definitions.Def_ModularCurve_MazurStepThreeInputs
public import Instance.AlgebraicGeometry_FppfSiteCohomology
public import Lemma.Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
public import Lemma.Definitions.Def_AlgebraicGeometry_FppfKummerProp17
public import Lemma.Definitions.Def_ModularCurve_JZeroToricTorsion
public import Structure.ModularCurve_JZeroNeronPrimaryTorsionSheaf
public import Def.ModularCurve_JZeroNeronPrimaryTorsionSheaf
set_option autoImplicit false


public section

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite


theorem torsionBySet_eisensteinMaximalIdeal_pow_le_eisensteinPrimaryTorsionBar
    (p q m : ℕ) [NeZero p] :
    letI := heckeModuleBar p
    (Submodule.torsionBySet HeckeAlg (JZero p)
      (↑((eisensteinMaximalIdeal p q) ^ m) : Set HeckeAlg)).toAddSubgroup
      ≤ eisensteinPrimaryTorsionBar p q m := by
  letI := heckeModuleBar p
  intro x hx
  refine ⟨?_, ?_⟩
  · have hq : ((q : HeckeAlg) ^ m) ∈ (eisensteinMaximalIdeal p q) ^ m := by
      apply Ideal.pow_mem_pow
      simp [eisensteinMaximalIdeal, Ideal.mem_comap]
    have hx' : ((q : HeckeAlg) ^ m) • x = 0 := (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨_, hq⟩
    change ((q : ℤ) ^ m) • x = 0
    rw [← Int.cast_smul_eq_zsmul HeckeAlg]
    simpa [Int.cast_pow, Int.cast_natCast] using hx'
  · exact AddSubgroup.mem_iSup_of_mem m hx


end ModularCurve
end
