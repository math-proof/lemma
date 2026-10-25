-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_LubinTateModule.lean: instance decls only.
import Mathlib
import Instance.MvFormalGroup_NegV2
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Lemma.CerednikDrinfeld.LubinTateModule

set_option autoImplicit false
set_option linter.unusedSectionVars false


universe u v in
set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace CerednikDrinfeld.LubinTate

universe u v

variable {p : ℕ} [Fact p.Prime]

instance instFintypeGaloisFieldTwo : Fintype (GaloisField p 2) := Fintype.ofFinite _

variable (p)

variable {p}


section Sigma

variable (p)

variable {p}

instance sigma_isComm : (sigma p).IsComm where
  comm i := by
    classical
    have hS : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆))
        fun j => X (Sum.inl j)) s) = 0 := by
      rintro (j | j) <;> exact constantCoeff_X _
    have hSv : (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆))
        fun j => X (Sum.inl j)) = fun s => X (Sum.swap s) := by
      funext s; rcases s with l | l <;> rfl
    show subst _ (sigmaSeries p) = sigmaSeries p
    refine eq_of_comm (constantCoeff_subst_of constantCoeff_sigmaSeries hS)
      constantCoeff_sigmaSeries ?_ comm_sigmaSeries ?_
    · rw [hSv]
      exact comm_subst_X comm_sigmaSeries _
    · intro t
      rw [coeff_single_subst_sigmaSeries hS, coeff_single_sigmaSeries]
      simp only [Sum.elim_inl, Sum.elim_inr, coeff_index_single_X]
      rcases t with l | l <;> rw [Fin.fin_one_eq_zero l] <;> simp

end Sigma

section Reduction

instance instIsCommMap {g : ℕ} {R S : Type*} [CommRing R] [CommRing S] (F : MvFormalGroup g R)
    [F.IsComm] (f : R →+* S) : (F.map f).IsComm := by
  constructor
  intro i
  have key := congrArg (MvPowerSeries.map f) (MvFormalGroup.IsComm.comm (F := F) i)
  have hS : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j) <;> exact constantCoeff_X _
  rw [map_subst hS] at key
  have hfam : (fun s => MvPowerSeries.map f (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      (fun j => X (Sum.inl j)) s))
      = Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) S))
        fun j => X (Sum.inl j) := by
    funext s
    rcases s with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, MvPowerSeries.map_X]
  rw [hfam] at key
  exact key

variable {B : Type u} [CommRing B]

variable (j : Zp2 p →+* B)

instance sigmaBar_isComm : (sigmaBar j).IsComm := instIsCommMap _ _

variable [CharP B p]

end Reduction

end CerednikDrinfeld.LubinTate

end
