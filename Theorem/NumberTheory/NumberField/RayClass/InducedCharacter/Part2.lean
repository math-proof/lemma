/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean -/

import Def.NumberTheory.NumberField.RayClass.Character
import Lemma.Nat.NumberField.RayClass.Character
import Def.NumberTheory.NumberField.RayClass.InducedCharacter
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Induced ray class characters (N428 Definition 22.12)

If `m1 ∣ m2`, a ray class character at `m2` is induced by one at `m1`
when their values agree on ideals coprime to `m2` under level change.
A character is primitive when it is induced only from the same modulus.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K] {m1 m2 : Modulus K}

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

end Modulus
end NumberField
