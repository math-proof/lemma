import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[Algebra_Etale_algHom_ext_of_forall_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_algHom_ext_of_forall_comp_eq.lean)
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

private lemma algHom_ext_of_points
  {K : Type*}
  [Field K]
  {Ω : Type*}
  [Field Ω]
  [Algebra K Ω]
  [IsAlgClosed Ω]
  {B : Type*} [Semiring B] [Algebra K B]
  {C : Type u} [CommRing C] [Algebra K C] [Algebra.Etale K C]
  {ψ₁ ψ₂ : B →ₐ[K] C} (h : ∀ χ : C →ₐ[K] Ω, χ.comp ψ₁ = χ.comp ψ₂) : ψ₁ = ψ₂ :=
  AlgHom.ext fun b =>
    points_separate_of_etale (fun χ => DFunLike.congr_fun (h χ) b)


@[path]
private lemma main
  [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Semiring B] [Algebra K B] [CommRing C] [Algebra K C] [Algebra.Etale K C]
  {ψ₁ ψ₂ : B →ₐ[K] C}
-- given
  (h : ∀ χ : C →ₐ[K] Ω, χ.comp ψ₁ = χ.comp ψ₂) :
-- imply
  ψ₁ = ψ₂ :=
-- proof
  algHom_ext_of_points h


-- created on 2026-10-10
