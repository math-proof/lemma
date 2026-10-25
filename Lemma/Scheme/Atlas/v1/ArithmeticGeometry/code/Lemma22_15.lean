import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.Lemma22_15
open Lemma22_15


namespace Lemma22_15

/--
[addPlace_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_15.lean)
-/
@[path]
lemma addPlace_self
  [DecidableEq Place]
  {D : Place → ℤ}
  {P : Place} :
-- imply
  addPlace D P P = D P + 1 := by
-- proof
  simp [addPlace]

end Lemma22_15

namespace Lemma22_15

/--
[addPlace_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_15.lean)
-/
@[path]
lemma addPlace_ne
  [DecidableEq Place]
  {D : Place → ℤ}
  {P Q : Place}
-- given
  (h : Q ≠ P) :
-- imply
  addPlace D P Q = D Q := by
-- proof
  simp [addPlace, Function.update_of_ne h]

end Lemma22_15

namespace Lemma22_15

/--
[le_addPlace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_15.lean)
-/
@[path]
lemma le_addPlace
  [DecidableEq Place]
  {D : Place → ℤ}
  {P : Place} :
-- imply
  D ≤ addPlace D P := by
-- proof
  intro Q
  by_cases h : Q = P
  · subst h; simp [addPlace]
  · exact le_of_eq (addPlace_ne D P Q h).symm

end Lemma22_15

namespace Lemma22_15

/--
[exists_maximal_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_15.lean)
-/
@[path]
lemma exists_maximal_divisor
  [DecidableEq Place]
  [Zero Ω]
  {ω : Ω}
-- given
  (omegaD : Ω → (Place → ℤ) → Prop)
  (adele_decomp : ∀ (ω : Ω) (D₁ D₂ : Place → ℤ) (P : Place), omegaD ω D₁ → omegaD ω D₂ → D₁ P < D₂ P → omegaD ω (addPlace D₁ P))
  (_hω : ω ≠ 0)
  (hex : ∃ D, omegaD ω D)
  (hfin : Set.Finite {D | omegaD ω D}) :
-- imply
  ∃ D, IsMaximalDivisorFor omegaD ω D := by
-- proof
  obtain ⟨D₀, hD₀⟩ := hex
  have hne : ({D | omegaD ω D} : Set (Place → ℤ)).Nonempty := ⟨D₀, hD₀⟩
  obtain ⟨m, hm⟩ := hfin.exists_maximal hne
  refine ⟨m, hm.prop, fun D' hD' => ?_⟩
  by_contra h_not_le
  simp only [Pi.le_def, not_forall] at h_not_le
  obtain ⟨P, hP⟩ := h_not_le
  push_neg at hP
  have h_in : omegaD ω (addPlace m P) := adele_decomp ω m D' P hm.prop hD' hP
  have h_le : addPlace m P ≤ m := hm.le_of_ge h_in (le_addPlace m P)
  exact absurd (h_le P) (by simp)

end Lemma22_15

namespace Lemma22_15

/--
[unique_maximal_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_15.lean)
-/
@[path]
lemma unique_maximal_divisor
  [DecidableEq Place]
  [Zero Ω]
  {ω : Ω}
  {D₁ D₂ : Place → ℤ}
-- given
  (omegaD : Ω → (Place → ℤ) → Prop)
  (h₁ : IsMaximalDivisorFor omegaD ω D₁)
  (h₂ : IsMaximalDivisorFor omegaD ω D₂) :
-- imply
  D₁ = D₂ :=
-- proof
  le_antisymm (h₂.2 D₁ h₁.1) (h₁.2 D₂ h₂.1)

end Lemma22_15

namespace Lemma22_15

/--
[exists_unique_maximal_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_15.lean)
-/
@[path]
lemma exists_unique_maximal_divisor
  [DecidableEq Place]
  [Zero Ω]
  {ω : Ω}
-- given
  (omegaD : Ω → (Place → ℤ) → Prop)
  (adele_decomp : ∀ (ω : Ω) (D₁ D₂ : Place → ℤ) (P : Place), omegaD ω D₁ → omegaD ω D₂ → D₁ P < D₂ P → omegaD ω (addPlace D₁ P))
  (hω : ω ≠ 0)
  (hex : ∃ D, omegaD ω D)
  (hfin : Set.Finite {D | omegaD ω D}) :
-- imply
  ∃! D, IsMaximalDivisorFor omegaD ω D := by
-- proof
  obtain ⟨D, hD⟩ := exists_maximal_divisor omegaD adele_decomp ω hω hex hfin
  exact ⟨D, hD, fun D' hD' => unique_maximal_divisor omegaD ω hD' hD⟩

end Lemma22_15


-- created on 2026-10-23
