import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec7ProductsSeparatedness
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Lec7
open scoped TensorProduct


namespace Lec7

/--
[separated_of_open_immersion_to_separated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ProductsSeparatedness.lean)
-/
@[path]
lemma separated_of_open_immersion_to_separated
  {X Y : Scheme.{u}}
  {f : X ⟶ Y}
  [IsOpenImmersion f]
  [Y.IsSeparated] :
-- imply
  X.IsSeparated := by
-- proof
  constructor
  have : IsSeparated f := inferInstance
  have : IsSeparated (terminal.from Y) := Scheme.IsSeparated.isSeparated_terminal_from
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _]
  infer_instance

end Lec7

namespace Lec7

/--
[prop9_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ProductsSeparatedness.lean)
-/
@[path]
lemma prop9_forward
  {X : Scheme.{u}}
  [X.IsSeparated]
  {U V : X.Opens}
-- given
  (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) :
-- imply
  IsAffineOpen (U ⊓ V) :=
-- proof
  hU.inf hV

end Lec7

namespace Lec7

/--
[prop9_separated_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ProductsSeparatedness.lean)
-/
@[path]
lemma prop9_separated_iff
  {X : Scheme.{u}} :
-- imply
  X.IsSeparated ↔ (∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) ∧ (∀ (W : (pullback (terminal.from X) (terminal.from X)).Opens), IsAffineOpen W → Function.Surjective ((pullback.diagonal (terminal.from X)).app W)) := by
-- proof
  rw [Scheme.isSeparated_iff, isSeparated_iff, isClosedImmersion_iff_isAffineHom]
  constructor
  · rintro ⟨hAff, hSurj⟩
    constructor
    · rw [isAffineHom_diagonal_iff] at hAff
      intro U V hU hV
      exact hAff ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV
    · exact hSurj
  · rintro ⟨hAff, hSurj⟩
    constructor
    · rw [isAffineHom_diagonal_iff]
      intro U _ V₁ _ V₂ _ hV₁ hV₂
      exact hAff V₁ V₂ hV₁ hV₂
    · exact hSurj

end Lec7

namespace Lec7

/--
[proj_is_separated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ProductsSeparatedness.lean)
-/
@[path]
lemma proj_is_separated
  {A : Type u}
  {σ : Type u}
  [CommRing A]
  [SetLike σ A]
  [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ}
  [GradedRing 𝒜] :
-- imply
  IsSeparated (Proj.toSpecZero 𝒜) :=
-- proof
  Proj.isSeparated 𝒜

end Lec7

namespace Lec7

/--
[separated_of_closed_immersion_to_separated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ProductsSeparatedness.lean)
-/
@[path]
lemma separated_of_closed_immersion_to_separated
  {X Y : Scheme.{u}}
  {f : X ⟶ Y}
  [IsClosedImmersion f]
  [Y.IsSeparated] :
-- imply
  X.IsSeparated := by
-- proof
  constructor
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _]
  infer_instance

end Lec7

namespace Lec7

/--
[separated_of_locally_closed_immersion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ProductsSeparatedness.lean)
-/
@[path]
lemma separated_of_locally_closed_immersion
  {X Z Y : Scheme.{u}}
  {f : X ⟶ Z}
  {g : Z ⟶ Y}
  [IsClosedImmersion f]
  [IsOpenImmersion g]
  [Y.IsSeparated] :
-- imply
  X.IsSeparated := by
-- proof
  have : Z.IsSeparated := separated_of_open_immersion_to_separated g
  exact separated_of_closed_immersion_to_separated f

end Lec7


-- created on 2026-10-23
