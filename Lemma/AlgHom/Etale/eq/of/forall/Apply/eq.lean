import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[Algebra_Etale_eq_of_forall_algHom_apply_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_eq_of_forall_algHom_apply_eq.lean)
-/

private lemma points_separate_of_etale
  {K : Type*}
  [Field K]
  {Ω : Type*}
  [Field Ω]
  [Algebra K Ω]
  [IsAlgClosed Ω]
  {B : Type u} [CommRing B] [Algebra K B] [Algebra.Etale K B]
  {x y : B} (h : ∀ χ : B →ₐ[K] Ω, χ x = χ y) : x = y := by
  obtain ⟨I, hfin, L, hfield, halg, e, hL⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K B).mp inferInstance
  have := hfin
  let : ∀ i, Field (L i) := hfield
  let : ∀ i, Algebra K (L i) := halg
  apply e.injective
  funext i
  have : Module.Finite K (L i) := (hL i).1
  apply (IsAlgClosed.lift (R := K) (S := L i) (M := Ω)).toRingHom.injective
  exact h (((IsAlgClosed.lift (M := Ω)).comp (Pi.evalAlgHom K L i)).comp e.toAlgHom)


@[path]
private lemma main
  [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [CommRing B] [Algebra K B] [Algebra.Etale K B]
  {x y : B}
-- given
  (h : ∀ χ : B →ₐ[K] Ω, χ x = χ y) :
-- imply
  x = y :=
-- proof
  points_separate_of_etale h


-- created on 2026-10-10
