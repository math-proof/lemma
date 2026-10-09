import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

/--
[AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero.lean)
-/
@[path]
private lemma main
  [Field C] [CharZero C]
  {X : Scheme.{0}} [IsIntegral X]
  {f : Spec (CommRingCat.of C) ⟶ X} :
-- imply
  CharZero X.functionField := by
-- proof
  have : CharZero ↑Γ(Spec (CommRingCat.of C), ⊤) :=
    (RingHom.charZero_iff (ϕ := (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
      (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective).1 inferInstance

  have : CharZero ↑Γ(X, ⊤) := (f.appTop).hom.charZero

  have := (Scheme.Opens.nonempty_iff (⊤ : X.Opens)).2 ⟨(inferInstance : Nonempty X).some, trivial⟩
  exact (RingHom.charZero_iff (X.germToFunctionField_injective ⊤)).1 inferInstance


-- created on 2026-10-05
