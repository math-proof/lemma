import Mathlib
import Lemma.Definitions.Def_MvFormalGroup_NegV2
import Lemma.Definitions.Def_MvFormalGroup_CartierModule
import Lemma.Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Lemma.Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Lemma.Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Lemma.Definitions.Def_MvFormalGroup_WittPointFamily

set_option autoImplicit false

noncomputable section

universe u v

open MvPowerSeries

namespace MvFormalGroup

namespace WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {τ : Type v}

theorem coeff_frobenius_eq_subst_frobPolyFam (x : WittVector p (MvPowerSeries τ R)) (n : ℕ) :
    (WittVector.frobenius x).coeff n = subst (fun m => x.coeff m) (frobPolyFam p R n) := by
  rw [WittVector.coeff_frobenius]
  change MvPolynomial.eval₂ (Int.castRingHom (MvPowerSeries τ R)) x.coeff (WittVector.frobeniusPoly p n) = _
  rw [frobPolyFam_apply, frobPoly_eq_map, subst_coe, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem frobenius_mem_int {x : WittVector p (MvPowerSeries τ R)} (hx : x ∈ seriesPoint p R τ) :
    WittVector.frobenius x ∈ seriesPoint p R τ := by
  have hfam : (fun n => (WittVector.frobenius x).coeff n) =
      fun n => subst (fun m => x.coeff m) (frobPolyFam p R n) :=
    funext (coeff_frobenius_eq_subst_frobPolyFam x)
  refine ⟨fun n => ?_, ?_⟩
  · rw [coeff_frobenius_eq_subst_frobPolyFam x]
    exact constantCoeff_subst_eq_zero hx.2 hx.1 (constantCoeff_frobPolyFam (p := p) (R := R) n)
  · rw [hfam]
    simpa only [coe_substAlgHom] using (hasSubst_frobPolyFam (p := p) (R := R)).comp hx.2

def frobIntPt : seriesPoint p R τ →+ seriesPoint p R τ where
  toFun x := ⟨WittVector.frobenius x, frobenius_mem_int x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp] theorem coe_frobIntPt (x : seriesPoint p R τ) :
    ((frobIntPt x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)) = WittVector.frobenius x :=
  rfl

theorem coeff_frobIntPt (x : seriesPoint p R τ) (n : ℕ) :
    ((frobIntPt x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n =
      subst (fun m => (x : WittVector p (MvPowerSeries τ R)).coeff m) (frobPolyFam p R n) :=
  coeff_frobenius_eq_subst_frobPolyFam (x : WittVector p (MvPowerSeries τ R)) n

theorem frobIntPt_eq_frobPt [CharP R p] (x : seriesPoint p R τ) : frobIntPt x = frobPt x :=
  Subtype.ext rfl

theorem frobIntPt_verPt (x : seriesPoint p R τ) : frobIntPt (verPt x) = p • x := by
  apply Subtype.ext
  rw [coe_frobIntPt, coe_verPt, WittVector.frobenius_verschiebung, AddSubgroup.coe_nsmul,
    nsmul_eq_mul, mul_comm]

theorem frobIntPt_teichPt (c : R) (x : seriesPoint p R τ) :
    frobIntPt (teichPt c x) = teichPt (c ^ p) (frobIntPt x) := by
  apply Subtype.ext
  rw [coe_frobIntPt, coe_teichPt, coe_teichPt, coe_frobIntPt, map_mul, WittVector.frobenius_teichmuller_eq,
    ← map_pow]

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}
  {τ : Type v}

theorem evalPt_frobIntPt [Φ.IsComm] (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) :
    evalPt f (WittLaw.frobIntPt w) = evalPt (verschiebungInt f) w :=
  evalPt_eq_evalPt_precomp WittLaw.isEndo_frobPolyFam f w _ fun n => WittLaw.coeff_frobIntPt w n

theorem evalPt_frobIntPt_iterate [Φ.IsComm] (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ)
    (m : ℕ) :
    evalPt f ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] w) =
      evalPt ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] f) w := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply, evalPt_frobIntPt, ih]

end CartierModule

end MvFormalGroup

end
