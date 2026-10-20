import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry


universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma isSeparated_iff_universallyClosed_diagonal
  {X Y : Scheme.{u}} (f : X ⟶ Y) :
-- imply
  IsSeparated f ↔ UniversallyClosed (pullback.diagonal f) := by
-- proof
  refine ⟨fun _ => inferInstance, fun _ => ⟨?_⟩⟩
  apply IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range

private lemma isSeparated_eq_diagonal_universallyClosed :
-- imply
  @IsSeparated = MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme.{u}) := by
-- proof
  ext X Y f
  rw [MorphismProperty.diagonal_iff]
  apply isSeparated_iff_universallyClosed_diagonal f

/--
[AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean)
-/
@[path]
private lemma main :
-- imply
  DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
-- proof
  rw [isSeparated_eq_diagonal_universallyClosed]
  infer_instance


-- created on 2026-10-20
