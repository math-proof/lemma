import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Module_exists_away_forall_nonempty_basis_tensorProduct_of_projective_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_exists_away_forall_nonempty_basis_tensorProduct_of_projective_of_finite.lean)
-/
@[main]
private lemma main
  {S : Type u} [CommRing S]
  {P : Type u} [AddCommGroup P] [Module S P] [Module.Finite S P] [Module.Projective S P]
  {p : PrimeSpectrum S} :
-- imply
  ∃ r : S, r ∉ p.asIdeal ∧
      ∀ (S' : Type u) [CommRing S'] [Algebra S S'] [IsLocalization.Away r S'],
        ∃ m : ℕ, Nonempty (Module.Basis (Fin m) S' (S' ⊗[S] P)) := by
-- proof
  classical
  have hfp : Module.FinitePresentation S P := Module.finitePresentation_of_projective S P
  have hfin : Module.Finite (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl P) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P)
  have hfree : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl P) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree', -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P)
    (Localization.AtPrime p.asIdeal)
  refine ⟨r, hr, fun S' _ _ _ => ?_⟩
  let A := Localization (Submonoid.powers r)
  haveI : Module.Free A (A ⊗[S] P) :=
    Module.Free.of_equiv (IsLocalizedModule.isBaseChange (Submonoid.powers r) A
      (LocalizedModule.mkLinearMap (Submonoid.powers r) P)).equiv.symm
  let e : A ≃ₐ[S] S' := Localization.algEquiv (Submonoid.powers r) S'
  letI : Algebra A S' := (e : A →+* S').toAlgebra
  haveI : IsScalarTower S A S' :=
    IsScalarTower.of_algebraMap_eq fun s => (e.commutes s).symm
  haveI : Module.Free S' (S' ⊗[A] (A ⊗[S] P)) := inferInstance
  haveI : Module.Free S' (S' ⊗[S] P) :=
    Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange S A S' S' P)
  rcases subsingleton_or_nontrivial S' with h | h
  · haveI : Subsingleton (S' ⊗[S] P) := Module.subsingleton S' _
    exact ⟨0, ⟨Module.Basis.empty _⟩⟩
  · exact ⟨_, ⟨Module.finBasis S' (S' ⊗[S] P)⟩⟩


-- created on 2026-10-05
