import Lemma.AutomorphicForm.ArithCuspRealization
import Lemma.AutomorphicForm.ProductionPinsCompact
import Lemma.AutomorphicForm.ArchWeightCharTransport
import Def.ModularForm_EisensteinChiNegThree
import Def.AutomorphicForm_ViaCompactCuspNotion

set_option autoImplicit false

open IsDedekindDomain NumberField EisensteinWeightOne CongruenceSubgroup
open scoped Manifold

noncomputable section

namespace AutomorphicForm


@[simp] theorem iotaZsqrtdNegTwo_apply (z : ℤ√(-2)) :
    iotaZsqrtdNegTwo z = (z.re : ℂ) + (z.im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I) := by
  simp [iotaZsqrtdNegTwo, Zsqrtd.lift]


theorem viaCompactCuspNotion_isCusp_iff {F : Type} [Field F] [NumberField F]
    (Φ : HeckeEigensystem F (ℤ√(-2))) :
    viaCompactCuspNotion.IsCusp F Φ ↔
      (∃ R : SmoothCuspRealizationAt F (productionPinsCompact F)
          ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          IsArchHolomorphicAt w hw R.toFun)) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))) :=
  Iff.rfl

theorem isArithCuspRealizableVia_of_viaCompactCuspNotion {F : Type} [Field F]
    [NumberField F] (Φ : HeckeEigensystem F (ℤ√(-2)))
    (h : viaCompactCuspNotion.IsCusp F Φ) :
    IsArithCuspRealizableVia F (productionPinsCompact F) iotaZsqrtdNegTwo Φ :=
  ⟨h.1.choose⟩

end AutomorphicForm

end
