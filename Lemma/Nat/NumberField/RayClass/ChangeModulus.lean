import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.ChangeModulus
open scoped nonZeroDivisors
open NumberField.Modulus


namespace NumberField.Modulus

/--
[rayGroupAmbient_le_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
lemma rayGroupAmbient_le_coprime
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  rayGroupAmbient m ≤ coprimeFractionalIdeals m := by
-- proof
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.property

end NumberField.Modulus

namespace NumberField.Modulus

/--
[CongruenceSubgroup.rayGroupAmbient_le_toAmbientSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
lemma CongruenceSubgroup.rayGroupAmbient_le_toAmbientSubgroup
  [Field K] [NumberField K]
  {m : Modulus K}
  {C : CongruenceSubgroup m} :
-- imply
  rayGroupAmbient m ≤ C.toAmbientSubgroup :=
-- proof
  Subgroup.map_mono C.rayGroup_le

end NumberField.Modulus

namespace NumberField.Modulus

/--
[coprimeFractionalIdeals_le_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
lemma coprimeFractionalIdeals_le_of_dvd
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
-- given
  (h : m2 ∣ m1) :
-- imply
  coprimeFractionalIdeals m1 ≤ coprimeFractionalIdeals m2 := by
-- proof
  intro x hx
  rw [mem_coprimeFractionalIdeals_iff] at hx ⊢
  have hparts := (dvd_unfold m2 m1).mp h
  simp only [finiteSupported] at hx ⊢
  intro v hv
  exact hx v (hparts.1.trans hv)

end NumberField.Modulus

namespace NumberField.Modulus

/--
[changeModulus_toAmbientSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
lemma changeModulus_toAmbientSubgroup
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {C1 : CongruenceSubgroup m1} :
-- imply
  (changeModulus C1 m2).toAmbientSubgroup =
    (C1.toAmbientSubgroup ⊓ coprimeFractionalIdeals m2) ⊔
    rayGroupAmbient m2 := by
-- proof
  unfold changeModulus CongruenceSubgroup.toAmbientSubgroup
    rayGroupAmbient
  rw [Subgroup.map_sup, Subgroup.map_comap_eq,
    Subgroup.range_subtype, inf_comm (coprimeFractionalIdeals m2) _]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[changeModulus_toAmbientSubgroup_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
lemma changeModulus_toAmbientSubgroup_of_dvd
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {C1 : CongruenceSubgroup m1}
-- given
  (hdiv : m2 ∣ m1) :
-- imply
  (changeModulus C1 m2).toAmbientSubgroup =
    C1.toAmbientSubgroup ⊔ rayGroupAmbient m2 := by
-- proof
  rw [changeModulus_toAmbientSubgroup]
  have hle : C1.toAmbientSubgroup ≤ coprimeFractionalIdeals m2 :=
    le_trans C1.toAmbientSubgroup_le
      (coprimeFractionalIdeals_le_of_dvd hdiv)
  rw [inf_eq_left.mpr hle]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[changeModulus_isEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
lemma changeModulus_isEquivalent
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {C1 : CongruenceSubgroup m1}
-- given
  (hdiv : m2 ∣ m1)
  (hcond : coprimeFractionalIdeals m1 ⊓ rayGroupAmbient m2 ≤ C1.toAmbientSubgroup) :
-- imply
  CongruenceSubgroupPair.IsEquivalent
    { modulus := by
-- proof
  have hC1 : C1.toAmbientSubgroup ≤ coprimeFractionalIdeals m1 :=
    C1.toAmbientSubgroup_le
  have hC1' : C1.toAmbientSubgroup ≤ coprimeFractionalIdeals m2 :=
    le_trans hC1 (coprimeFractionalIdeals_le_of_dvd hdiv)
  have hcond' : rayGroupAmbient m2 ⊓ coprimeFractionalIdeals m1 ≤
    C1.toAmbientSubgroup := by
    rwa [inf_comm]
  change coprimeFractionalIdeals m1 ⊓
    (changeModulus C1 m2).toAmbientSubgroup =
    coprimeFractionalIdeals m2 ⊓ C1.toAmbientSubgroup
  rw [changeModulus_toAmbientSubgroup_of_dvd C1 hdiv,
    inf_comm (coprimeFractionalIdeals m1) _,
    sup_inf_assoc_of_le _ hC1, sup_eq_left.mpr hcond',
    inf_eq_right.mpr hC1']

end NumberField.Modulus

namespace NumberField.Modulus

/--
[exists_equivalent_iff_changeModulus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
lemma exists_equivalent_iff_changeModulus
  [Field K] [NumberField K]
  {m1 : Modulus K}
  {C1 : CongruenceSubgroup m1}
  {m2 : Modulus K}
-- given
  (hdiv : m2 ∣ m1) :
-- imply
  (∃ C2 : CongruenceSubgroup m2,
    CongruenceSubgroupPair.IsEquivalent
    { modulus := by
-- proof
  constructor
  · rintro ⟨C2, hC2⟩
    have hC1' : C1.toAmbientSubgroup ≤ coprimeFractionalIdeals m2 :=
      le_trans C1.toAmbientSubgroup_le
        (coprimeFractionalIdeals_le_of_dvd hdiv)
    have heq :=
      (CongruenceSubgroupPair.isEquivalent_iff _ _).mp hC2
    calc coprimeFractionalIdeals m1 ⊓ rayGroupAmbient m2
      ≤ coprimeFractionalIdeals m1 ⊓ C2.toAmbientSubgroup :=
        inf_le_inf_left _
          C2.rayGroupAmbient_le_toAmbientSubgroup
      _ = C1.toAmbientSubgroup := by
        rw [heq, inf_eq_right.mpr hC1']
  · intro hcond
    exact ⟨changeModulus C1 m2,
      changeModulus_isEquivalent C1 hdiv hcond⟩

end NumberField.Modulus


-- created on 2026-10-20
-- updated on 2026-10-23
