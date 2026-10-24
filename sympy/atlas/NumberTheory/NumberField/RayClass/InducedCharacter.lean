/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.Character
import Lemma.Nat.NumberField.RayClass.Character
/-!
# Induced ray class characters (N428 Definition 22.12)

If `m1 ∣ m2`, a ray class character at `m2` is induced by one at `m1`
when their values agree on ideals coprime to `m2` under level change.
A character is primitive when it is induced only from the same modulus.
-/

@[expose] noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K] {m1 m2 : Modulus K}

/-- Finite exponents are monotone under modulus divisibility. -/
theorem finiteExponent_le_of_dvd (h : m1 ∣ m2)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    finiteExponent m1 v ≤ finiteExponent m2 v := by
  have hfin := ((dvd_unfold m1 m2).mp h).1
  have hne : (m2.finitePart : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa using mem_nonZeroDivisors_iff_ne_zero.mp m2.finitePart.property
  unfold finiteExponent
  exact FractionalIdeal.count_mono K v (FractionalIdeal.coeIdeal_ne_zero.mpr hne)
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hfin)

private theorem coprime_le_of_dvd (h : m1 ∣ m2) :
    coprimeFractionalIdeals m2 ≤ coprimeFractionalIdeals m1 := by
  intro u hu v hv
  exact hu v (le_trans ((dvd_unfold m1 m2).mp h).1 hv)

/-- Natural level-change map on coprime fractional ideals. -/
def coprimeInclusion (h : m1 ∣ m2) :
    coprimeFractionalIdeals m2 →* coprimeFractionalIdeals m1 :=
  Subgroup.inclusion (coprime_le_of_dvd h)

/-- Ray-one mod `m2` implies ray-one mod `m1`. -/
theorem IsRayElementOne.of_dvd (h : m1 ∣ m2) {x : Kˣ}
    (hx : IsRayElementOne m2 x) : IsRayElementOne m1 x := by
  have hfin := ((dvd_unfold m1 m2).mp h).1
  have hinf := ((dvd_unfold m1 m2).mp h).2
  refine ⟨Subgroup.mem_comap.mpr (coprime_le_of_dvd h (Subgroup.mem_comap.mp hx.1)),
    ?_, ?_⟩
  · intro v hv
    rcases hx.2.1 v (le_trans hfin hv) with h1 | hle
    · exact Or.inl h1
    · exact Or.inr (le_trans (finiteExponent_le_of_dvd h v) hle)
  · intro w hw
    exact hx.2.2 w (Finset.mem_coe.mp (hinf (Finset.mem_coe.mpr hw)))

theorem rayGenerators_map_of_dvd (h : m1 ∣ m2) (y : coprimeFractionalIdeals m2)
    (hy : y ∈ rayGenerators m2) : coprimeInclusion h y ∈ rayGroup m1 := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hx1 := IsRayElementOne.of_dvd h hx
  have heq : coprimeInclusion h ⟨toPrincipalIdeal (𝓞 K) K x, Subgroup.mem_comap.mp hx.1⟩ =
      ⟨toPrincipalIdeal (𝓞 K) K x, Subgroup.mem_comap.mp hx1.1⟩ := Subtype.ext rfl
  rw [heq]
  exact mem_rayGroup_of_isRayElementOne m1 x hx1

theorem rayGroup_le_comap_of_dvd (h : m1 ∣ m2) :
    rayGroup m2 ≤ (rayGroup m1).comap (coprimeInclusion h) := by
  apply rayGroup_closure_le
  intro y hy
  exact rayGenerators_map_of_dvd h y hy

/-- Level-change map on ray class groups. -/
def RayClassGroup.mapOfDvd (h : m1 ∣ m2) : RayClassGroup m2 →* RayClassGroup m1 :=
  QuotientGroup.map (rayGroup m2) (rayGroup m1) (coprimeInclusion h) (rayGroup_le_comap_of_dvd h)

/-- `mapOfDvd` on canonical representatives. -/
@[simp] theorem RayClassGroup.mapOfDvd_rayClassMap (h : m1 ∣ m2)
    (x : coprimeFractionalIdeals m2) :
    mapOfDvd h (rayClassMap m2 x) = rayClassMap m1 (coprimeInclusion h x) := by
  simp only [mapOfDvd, rayClassMap, QuotientGroup.mk'_apply, QuotientGroup.map_mk]

/-- A character at `m2` induced by one at `m1` via level change. -/
def RayClassCharacter.IsInducedBy (chi2 : RayClassCharacter m2)
    (chi1 : RayClassCharacter m1) (h : m1 ∣ m2) : Prop :=
  chi2 = chi1.comp (RayClassGroup.mapOfDvd h)

/-- A character is primitive if induced only from the same modulus. -/
def RayClassCharacter.IsPrimitive (chi : RayClassCharacter m2) : Prop :=
  ∀ (m0 : Modulus K) (chi0 : RayClassCharacter m0) (h : m0 ∣ m2),
    chi.IsInducedBy chi0 h → m0 = m2
end Modulus
end NumberField
