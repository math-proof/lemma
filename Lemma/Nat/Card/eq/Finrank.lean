import Mathlib
import sympy.Basic


/--
[Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed.lean)
-/
@[main]
private lemma main
  [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R] [Algebra.Etale k R] :
-- imply
  Nat.card (R →ₐ[k] k) = Module.finrank k R := by
-- proof
  classical
  obtain ⟨ι, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k R).mp ‹_›
  have : Fintype ι := Fintype.ofFinite ι

  have hLk : ∀ i, Nonempty (L i ≃ₐ[k] k) := fun i => by
    have := (hL i).1
    have : Algebra.IsIntegral k (L i) := Algebra.IsIntegral.of_finite k (L i)
    exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (L i))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩

  let f : R ≃ₐ[k] (ι → k) := e.trans (AlgEquiv.piCongrRight fun i => (hLk i).some)
  have hrk : Module.finrank k R = Fintype.card ι := by
    rw [LinearEquiv.finrank_eq f.toLinearEquiv, Module.finrank_pi]

  have heval : Function.Bijective (fun i : ι => Pi.evalAlgHom k (fun _ => k) i) := by
    refine ⟨fun i j hij => ?_, fun φ => (AlgHom.eq_piEvalAlgHom φ).imp fun _ h => h.symm⟩
    have := DFunLike.congr_fun hij (Pi.single i 1)
    simp only [Pi.evalAlgHom_apply, Pi.single_apply] at this
    by_contra hne; simp [if_neg (Ne.symm hne)] at this
  have hcard : Nat.card (R →ₐ[k] k) = Fintype.card ι := by
    rw [Nat.card_congr (AlgEquiv.arrowCongr f AlgEquiv.refl),
      ← Nat.card_eq_fintype_card (α := ι),
      Nat.card_eq_of_bijective _ heval]
  rw [hrk, hcard]


-- created on 2026-10-05
