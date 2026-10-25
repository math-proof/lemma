-- Carved from Lemma/Definitions/Def_LocalGL2_Kirillov.lean: instance decls only.
import Mathlib
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Def.LocalGL2_Kirillov
import Notation.LocalGL2_Kirillov
import Abbrev.LocalGL2_Kirillov
import Lemma.Int.V.eq.R
import Lemma.Nat.IsCompactIntegers
import Lemma.Nat.IsCompactValuationEqOne
import Lemma.Complex.isOpen_radiusBall
import Lemma.Int.IsOpenUnitBall
import Lemma.Int.U.in.UmV.is.UFnSub.lt.WithZero_Multiplicative
import Lemma.Int.X.eq.U
import Lemma.Int.SetOfLtUFnSubR.in.NhdsY
import Lemma.Nat.VU.eq.One

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open scoped Classical LocalGL2_Kirillov

noncomputable section

namespace LocalGL2.Kirillov

open AutomorphicForm IsDedekindDomain NumberField

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

instance finite_Qm (δ : Γ) : Finite (Qm v δ) := by
  obtain ⟨T, hT, hcover⟩ := (Nat.IsCompactValuationEqOne v).elim_nhds_subcover
    (fun y => {x : F | Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ))}) (fun y _ => Int.SetOfLtUFnSubR.in.NhdsY v y δ)

  have hsurj : ∀ q : Qm v δ, ∃ t ∈ T, ∃ u : UF v, ((u : Fx) : F) = t ∧ (u : Qm v δ) = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : ((x : Fx) : F) ∈ {x : F | Valued.v x = 1} := Nat.VU.eq.One v x
    have hxU := hcover hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hxU
    obtain ⟨t, htT, hxt⟩ := hxU
    have ht1 : Valued.v t = 1 := hT t htT
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht1
    refine ⟨t, htT, ⟨Units.mk0 t ht0, ?_⟩, rfl, ?_⟩
    · show Valued.v ((Units.mk0 t ht0 : Fx) : F) = 1
      simpa using ht1
    · exact (Int.X.eq.U v δ _ _ (by simpa using hxt)).symm
  choose ft hftT fu hfu hfq using hsurj

  have hinj : Function.Injective (fun q : Qm v δ => (⟨ft q, hftT q⟩ : T)) := by
    intro q₁ q₂ h
    have h' : ft q₁ = ft q₂ := congrArg Subtype.val h
    rw [← hfq q₁, ← hfq q₂]
    have hu : ((fu q₁ : Fx) : F) = ((fu q₂ : Fx) : F) := by rw [hfu, hfu, h']
    have hu' : fu q₁ = fu q₂ := Subtype.ext (Units.ext hu)
    rw [hu']
  exact Finite.of_injective _ hinj

instance fintype_Qm (δ : Γ) : Fintype (Qm v δ) := Fintype.ofFinite _


instance addCommGroup_additive_Qm (δ : Γ) : AddCommGroup (Additive (Qm v δ)) :=
  @Additive.addCommGroup _ (QuotientGroup.Quotient.commGroup _)

instance finite_additive_Qm (δ : Γ) : Finite (Additive (Qm v δ)) := Finite.of_equiv _ Additive.ofMul

instance addCommGroup_Ch (δ : Γ) : AddCommGroup (Ch v δ) := charAddCommGroup (A := Additive (Qm v δ))

instance fintype_Ch (δ : Γ) : Fintype (Ch v δ) := charFintype (A := Additive (Qm v δ))

instance decidableEq_Ch (δ : Γ) : DecidableEq (Ch v δ) := Classical.decEq _


end LocalGL2.Kirillov

end
