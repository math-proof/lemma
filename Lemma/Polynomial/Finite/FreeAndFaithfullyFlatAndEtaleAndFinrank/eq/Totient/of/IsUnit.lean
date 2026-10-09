import Mathlib
import sympy.Basic

open Polynomial

/--
[AdjoinRoot_finite_free_faithfullyFlat_etale_cyclotomic_of_isUnit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdjoinRoot_finite_free_faithfullyFlat_etale_cyclotomic_of_isUnit.lean)
-/

noncomputable def sepPair
  {R : Type u}
  [CommRing R]
  (f : R[X]) (hf : f.Monic) (hsep : f.Separable) : StandardEtalePair R where
  f := f
  monic_f := hf
  g := 1
  cond := by
    obtain ⟨a, b, hab⟩ := hsep
    exact ⟨b, a, 0, by rw [pow_zero, ← hab]; ring⟩

lemma sepPair_f
  {R : Type u}
  [CommRing R]
  (f : R[X]) (hf : f.Monic) (hsep : f.Separable) : (sepPair f hf hsep).f = f := rfl

lemma sepPair_g
  {R : Type u}
  [CommRing R]
  (f : R[X]) (hf : f.Monic) (hsep : f.Separable) : (sepPair f hf hsep).g = 1 := rfl

noncomputable def sepPresentation
  {R : Type u}
  [CommRing R]
  (f : R[X]) (hf : f.Monic) (hsep : f.Separable) :
  StandardEtalePresentation R (AdjoinRoot f) where
  __ := sepPair f hf hsep
  x := AdjoinRoot.root f
  hasMap := ⟨by rw [sepPair_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self],
    by simp [sepPair_g]⟩
  lift_bijective := by
    have hX : (sepPair f hf hsep).HasMap (AdjoinRoot.root f) :=
      ⟨by rw [sepPair_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self],
       by simp [sepPair_g]⟩
    set P := sepPair f hf hsep
    have hzero : Polynomial.aeval P.X f = 0 := by
      have := P.hasMap_X.1
      rwa [sepPair_f] at this
    let ψ : AlgHom R (AdjoinRoot f) P.Ring :=
      AdjoinRoot.liftAlgHom f (Algebra.ofId R P.Ring) P.X hzero
    have hroot : ψ (AdjoinRoot.root f) = P.X :=
      AdjoinRoot.liftAlgHom_root f (Algebra.ofId R P.Ring) P.X hzero
    refine (AlgEquiv.ofAlgHom (P.lift _ hX) ψ ?_ ?_).bijective
    ·
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, hroot, StandardEtalePair.lift_X, AlgHom.id_apply]
    ·
      apply StandardEtalePair.hom_ext
      rwa [AlgHom.comp_apply, StandardEtalePair.lift_X]

private lemma isStandardEtale_adjoinRoot
  {R : Type u}
  [CommRing R]
  (f : R[X]) (hf : f.Monic) (hsep : f.Separable) :
  Algebra.IsStandardEtale R (AdjoinRoot f) :=
  ⟨⟨sepPresentation f hf hsep⟩⟩

private lemma separable_cyclotomic
  {R : Type u}
  [CommRing R]
  (m : ℕ) (hm : IsUnit ((m : ℕ) : R)) : (cyclotomic m R).Separable := by
  have h1 : (X ^ m - C ((1 : Rˣ) : R)).Separable := separable_X_pow_sub_C_unit 1 hm
  rw [Units.val_one, C_1] at h1
  exact h1.of_dvd (cyclotomic.dvd_X_pow_sub_one m R)


@[path]
private lemma main
  {𝒪 : Type u} [CommRing 𝒪]
  {m : ℕ}
-- given
  (hm : IsUnit ((m : ℕ) : 𝒪)) :
-- imply
  Module.Finite 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) ∧ Module.Free 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) ∧
      Module.FaithfullyFlat 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) ∧ Algebra.Etale 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) ∧
      (Nontrivial 𝒪 → Module.finrank 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) = Nat.totient m) := by
-- proof
  classical
  have hmon : (cyclotomic m 𝒪).Monic := cyclotomic.monic m 𝒪
  have hfin : Module.Finite 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) := hmon.finite_adjoinRoot
  let B := AdjoinRoot.powerBasis' (R := 𝒪) hmon
  have hfree : Module.Free 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) := Module.Free.of_basis B.basis
  have : Algebra.IsStandardEtale 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) :=
    isStandardEtale_adjoinRoot _ hmon (separable_cyclotomic m hm)
  have het : Algebra.Etale 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) := inferInstance
  have hdim : ∀ [Nontrivial 𝒪], B.dim = Nat.totient m := fun {_} => by
    rw [AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic]
  have hff : Module.FaithfullyFlat 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) := by
    obtain h𝒪 | h𝒪 := subsingleton_or_nontrivial 𝒪
    · exact ⟨fun I hI => absurd (Subsingleton.elim I ⊤) hI.ne_top⟩
    ·
      have hm0 : m ≠ 0 := by rintro rfl; simp at hm
      have hpos : 0 < B.dim := by rw [hdim]; exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm0)
      have : Nontrivial (AdjoinRoot (cyclotomic m 𝒪)) :=
        nontrivial_of_ne (B.basis ⟨0, hpos⟩) 0 (B.basis.ne_zero _)
      exact inferInstance
  refine ⟨hfin, hfree, hff, het, fun h𝒪 => ?_⟩
  rw [Module.finrank_eq_card_basis B.basis, Fintype.card_fin, hdim]


-- created on 2026-10-09
