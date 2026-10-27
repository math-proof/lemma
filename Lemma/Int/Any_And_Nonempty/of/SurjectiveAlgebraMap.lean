import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial
open scoped TensorProduct


/--
[Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_surjective.lean)
-/
@[path]
private lemma main
  {C C₀ : Type} [CommRing C] [CommRing C₀] [Algebra C C₀]
  {S₀ : Type} [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀]
-- given
  (hC : Function.Surjective (algebraMap C C₀)) :
-- imply
  ∃ (S : Type) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧ Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) := by
-- proof
  classical
  obtain ⟨P₀⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := C₀) (S := S₀)
  obtain hC₀ | hC₀ := subsingleton_or_nontrivial C₀
  ·
    have : Subsingleton S₀ := Module.subsingleton C₀ S₀
    refine ⟨C, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
    apply AlgEquiv.ofBijective ((Algebra.ofId C₀ S₀).comp (Algebra.TensorProduct.rid C C₀ C₀).toAlgHom)
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
  ·
    set φ : C →+* C₀ := algebraMap C C₀ with hφ
    obtain ⟨f, hf, -, hfm⟩ := lifts_and_degree_eq_and_monic (f := φ) ((mem_lifts _).mpr (map_surjective φ hC P₀.f)) P₀.monic_f
    obtain ⟨p₁, p₂, n, hP⟩ := P₀.cond
    obtain ⟨g, hg⟩ := map_surjective φ hC P₀.g
    obtain ⟨q₁, hq₁⟩ := map_surjective φ hC p₁
    obtain ⟨q₂, hq₂⟩ := map_surjective φ hC p₂
    let P : StandardEtalePair C :=
      { f := f, monic_f := hfm, g := g * (derivative f * q₁ + f * q₂), cond := ⟨g * q₁, g * q₂, 1, by ring⟩ }
    have hPf : P.f.map φ = P₀.f := hf
    have hPg : P.g.map φ = P₀.g ^ (n + 1) := by
      show (g * (derivative f * q₁ + f * q₂)).map φ = P₀.g ^ (n + 1)
      simp [← derivative_map, hf, hg, hq₁, hq₂, hP]
      ring
    let _ : Algebra C S₀ := ((algebraMap C₀ S₀).comp φ).toAlgebra
    have : IsScalarTower C C₀ S₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have key : ∀ (T : Type) [CommRing T] [Algebra C₀ T] [Algebra C T] [IsScalarTower C C₀ T] (t : T), P.HasMap t ↔ P₀.HasMap t := by
      intro T _ _ _ _ t
      simp [StandardEtalePair.HasMap]
      rw [← aeval_map_algebraMap C₀ t P.f, ← aeval_map_algebraMap C₀ t P.g, ← hφ, hPf, hPg, map_pow, isUnit_pow_iff (Nat.succ_ne_zero n)]
    have h1 : P.HasMap P₀.x := (key S₀ P₀.x).mpr P₀.hasMap
    have h2' : P.HasMap ((1 : C₀) ⊗ₜ[C] P.X) :=
      (StandardEtalePair.hasMap_X (P := P)).map (Algebra.TensorProduct.includeRight (R := C) (A := C₀) (B := P.Ring))
    have h2 : P₀.HasMap ((1 : C₀) ⊗ₜ[C] P.X) := (key (C₀ ⊗[C] P.Ring) _).mp h2'
    let F : C₀ ⊗[C] P.Ring →ₐ[C₀] S₀ :=
      Algebra.TensorProduct.lift (Algebra.ofId C₀ S₀) (P.lift P₀.x h1) (fun _ _ => .all _ _)
    let G : S₀ →ₐ[C₀] C₀ ⊗[C] P.Ring := (P₀.lift ((1 : C₀) ⊗ₜ[C] P.X) h2).comp P₀.equivRing.toAlgHom
    have hF : F ((1 : C₀) ⊗ₜ[C] P.X) = P₀.x := by
      simp [F, Algebra.TensorProduct.lift_tmul, StandardEtalePair.lift_X]
    have hG : G P₀.x = (1 : C₀) ⊗ₜ[C] P.X := by
      simp [G, StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X]
    refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, ⟨AlgEquiv.ofAlgHom F G ?_ ?_⟩⟩
    ·
      apply P₀.hom_ext
      simp [AlgHom.comp_apply, AlgHom.id_apply, hG, hF]
    ·
      apply Algebra.TensorProduct.ext
      · apply Subsingleton.elim
      ·
        apply StandardEtalePair.hom_ext
        simp [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply, hF, hG]


-- created on 2026-10-13
