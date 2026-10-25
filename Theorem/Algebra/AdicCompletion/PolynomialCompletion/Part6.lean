import Mathlib
import Def.Algebra.AdicCompletion.PolynomialCompletion.Part5
set_option autoImplicit false


namespace AdicCompletion

variable {R : Type*} [CommRing R] (q : Ideal R) [q.IsMaximal]

open IsLocalRing

@[simp] theorem localizationEquiv_of (x : R) :
    localizationEquiv q (of q R x) = of _ _ (algebraMap R (Localization.AtPrime q) x) :=
  ofLevelwiseEquiv_of _ _ _ _ x _ fun n => Localization.AtPrime.quotientPowEquiv_mk q n x

end AdicCompletion

namespace MvPolynomial

variable {σ : Type*} {k : Type*} [Field k]

theorem idealOfVars_eq_ker_constantCoeff :
    idealOfVars σ k = RingHom.ker (constantCoeff : MvPolynomial σ k →+* k) := by
  apply le_antisymm
  · rw [idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact constantCoeff_X k i
  · intro p hp
    rw [idealOfVars, ← Set.image_univ, mem_ideal_span_X_image]
    intro m hm
    by_contra! h
    have : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
    subst this
    exact (mem_support_iff.mp hm) hp

theorem idealOfVars_isMaximal : (idealOfVars σ k).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C σ a⟩

theorem eq_idealOfVars_of_X_mem (q : Ideal (MvPolynomial σ k)) [hq : q.IsMaximal] (hX : ∀ i, X i ∈ q) :
    q = idealOfVars σ k := by
  refine ((idealOfVars_isMaximal (σ := σ) (k := k)).eq_of_le hq.ne_top ?_).symm
  rw [idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hX i

end MvPolynomial
