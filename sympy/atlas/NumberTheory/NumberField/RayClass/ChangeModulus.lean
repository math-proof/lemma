/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.CongruenceEquivalence
/-!
# Change of modulus (ATLAS NumberTheoryI item N422 / Lemma 22.5)

Fixed-modulus equivalence criterion: for moduli with `m2 ∣ m1`, a congruence
subgroup at `m1` admits an equivalent congruence subgroup at the fixed modulus
`m2` if and only if it already contains the part of the `m2`-ray group that is
coprime to `m1`, i.e. `coprimeFractionalIdeals m1 ⊓ rayGroupAmbient m2 ≤ C1`.

The definition `changeModulus` is the canonical witness: the pullback of `C1`
to the `m2`-coprime ideals joined with the `m2`-ray group, which is equivalent
to `C1` whenever the criterion holds.
-/

noncomputable section

open scoped nonZeroDivisors

namespace NumberField.Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Ambient ray group in the ambient fractional-ideal units. -/
def rayGroupAmbient (m : Modulus K) : Subgroup ((FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  (rayGroup m).map (coprimeFractionalIdeals m).subtype

/-- The ambient ray group lies in the coprime fractional ideals. -/
theorem rayGroupAmbient_le_coprime (m : Modulus K) :
    rayGroupAmbient m ≤ coprimeFractionalIdeals m := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.property

/-- Ambient ray is contained in every congruence ambient subgroup. -/
theorem CongruenceSubgroup.rayGroupAmbient_le_toAmbientSubgroup
    {m : Modulus K} (C : CongruenceSubgroup m) :
    rayGroupAmbient m ≤ C.toAmbientSubgroup :=
  Subgroup.map_mono C.rayGroup_le

/-- Coprime fractional ideals are antitone under modulus divisibility. -/
theorem coprimeFractionalIdeals_le_of_dvd {m1 m2 : Modulus K}
    (h : m2 ∣ m1) :
    coprimeFractionalIdeals m1 ≤ coprimeFractionalIdeals m2 := by
  intro x hx
  rw [mem_coprimeFractionalIdeals_iff] at hx ⊢
  have hparts := (dvd_unfold m2 m1).mp h
  simp only [finiteSupported] at hx ⊢
  intro v hv
  exact hx v (hparts.1.trans hv)

/-- Change of modulus by pullback joined with the ray group. -/
def changeModulus {m1 : Modulus K} (C1 : CongruenceSubgroup m1)
    (m2 : Modulus K) : CongruenceSubgroup m2 where
  toSubgroup :=
    C1.toAmbientSubgroup.comap (coprimeFractionalIdeals m2).subtype ⊔
      rayGroup m2
  rayGroup_le := le_sup_right

/-- Ambient subgroup of `changeModulus`: pullback of `C1` joined
with the ambient ray group. -/
theorem changeModulus_toAmbientSubgroup {m1 m2 : Modulus K}
    (C1 : CongruenceSubgroup m1) :
    (changeModulus C1 m2).toAmbientSubgroup =
      (C1.toAmbientSubgroup ⊓ coprimeFractionalIdeals m2) ⊔
        rayGroupAmbient m2 := by
  unfold changeModulus CongruenceSubgroup.toAmbientSubgroup
    rayGroupAmbient
  rw [Subgroup.map_sup, Subgroup.map_comap_eq,
    Subgroup.range_subtype, inf_comm (coprimeFractionalIdeals m2) _]

/-- Simplified ambient form when `m2 ∣ m1`: `C1` already lies
in the coprime ideals for `m2`. -/
theorem changeModulus_toAmbientSubgroup_of_dvd {m1 m2 : Modulus K}
    (C1 : CongruenceSubgroup m1) (hdiv : m2 ∣ m1) :
    (changeModulus C1 m2).toAmbientSubgroup =
      C1.toAmbientSubgroup ⊔ rayGroupAmbient m2 := by
  rw [changeModulus_toAmbientSubgroup]
  have hle : C1.toAmbientSubgroup ≤ coprimeFractionalIdeals m2 :=
    le_trans C1.toAmbientSubgroup_le
      (coprimeFractionalIdeals_le_of_dvd hdiv)
  rw [inf_eq_left.mpr hle]

/-- The canonical change of modulus is equivalent to the original pair. -/
theorem changeModulus_isEquivalent {m1 m2 : Modulus K}
    (C1 : CongruenceSubgroup m1) (hdiv : m2 ∣ m1)
    (hcond : coprimeFractionalIdeals m1 ⊓ rayGroupAmbient m2 ≤
      C1.toAmbientSubgroup) :
    CongruenceSubgroupPair.IsEquivalent
      { modulus := m1, subgroup := C1 }
      { modulus := m2, subgroup := changeModulus C1 m2 } := by
  have hC1 : C1.toAmbientSubgroup ≤ coprimeFractionalIdeals m1 :=
    C1.toAmbientSubgroup_le
  have hC1' : C1.toAmbientSubgroup ≤ coprimeFractionalIdeals m2 :=
    le_trans hC1 (coprimeFractionalIdeals_le_of_dvd hdiv)
  have hcond' : rayGroupAmbient m2 ⊓ coprimeFractionalIdeals m1 ≤
      C1.toAmbientSubgroup := by
    rw [inf_comm]
    exact hcond
  change coprimeFractionalIdeals m1 ⊓
      (changeModulus C1 m2).toAmbientSubgroup =
    coprimeFractionalIdeals m2 ⊓ C1.toAmbientSubgroup
  rw [changeModulus_toAmbientSubgroup_of_dvd C1 hdiv,
    inf_comm (coprimeFractionalIdeals m1) _,
    sup_inf_assoc_of_le _ hC1, sup_eq_left.mpr hcond',
    inf_eq_right.mpr hC1']

/-- Exact N422 criterion: an equivalent pair at `m2` exists iff the ray
condition holds at `m1`. -/
theorem exists_equivalent_iff_changeModulus {m1 : Modulus K}
    (C1 : CongruenceSubgroup m1) {m2 : Modulus K} (hdiv : m2 ∣ m1) :
    (∃ C2 : CongruenceSubgroup m2,
      CongruenceSubgroupPair.IsEquivalent
        { modulus := m1, subgroup := C1 }
        { modulus := m2, subgroup := C2 }) ↔
      coprimeFractionalIdeals m1 ⊓ rayGroupAmbient m2 ≤
        C1.toAmbientSubgroup := by
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
