module

public import Mathlib
public import Theorem.MvPowerSeries.CartierModule
public import Theorem.PowerSeries.CartierModuleHomothety
public import Theorem.MvPowerSeries.CartierModuleWittAction
public import Theorem.MvPolynomial.CartierModuleIntVerschiebung
public import Theorem.MvPowerSeries.SpecialFormalModule
public import Theorem.FormalGroup.CartierGradedPiece
public import Theorem.Fin.GradedCartierModuleData

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries

namespace WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

omit hp in

public theorem hasSubst_subst_comp {σ τ υ : Type*} {a : σ → MvPowerSeries τ R}
    {b : τ → MvPowerSeries υ R} (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (fun s => subst b (a s)) := by
  simpa only [coe_substAlgHom] using ha.comp hb


public theorem verschiebung_cVec {τ : Type} (w : WittVector p R) :
    WittVector.verschiebung (cVec p (τ := τ) w) = cVec p (WittVector.verschiebung w) :=
  (WittVector.map_verschiebung _ w).symm


public theorem mulPoly_verschiebung_zero (w : WittVector p R) :
    mulPoly p (WittVector.verschiebung w) 0 = 0 := by
  show (cVec p (WittVector.verschiebung w) * xTaut p R).coeff 0 = 0
  rw [← verschiebung_cVec, ← WittVector.verschiebung_mul_frobenius]
  exact WittVector.verschiebung_coeff_zero _


public theorem mulPoly_verschiebung_succ (w : WittVector p R) (n : ℕ) :
    mulPoly p (WittVector.verschiebung w) (n + 1) =
      (cVec p w * WittVector.frobenius (xTaut p R)).coeff n := by
  show (cVec p (WittVector.verschiebung w) * xTaut p R).coeff (n + 1) = _
  rw [← verschiebung_cVec, ← WittVector.verschiebung_mul_frobenius]
  exact WittVector.verschiebung_coeff_succ _ n


public theorem subst_frobPolyFam_mulFam (w : WittVector p R) (n : ℕ) :
    subst (frobPolyFam p R) (mulFam p w n) =
      (((cVec p w * WittVector.frobenius (xTaut p R)).coeff n : MvPolynomial ℕ R) :
        MvPowerSeries ℕ R) := by
  have hf : frobPolyFam p R = fun m => (frobPoly p R m : MvPowerSeries ℕ R) := rfl
  rw [hf, mulFam_apply, ← coe_aeval, aeval_mulPoly, mk_frobPoly]


public theorem hasSubst_mulFam_frobPolyFam (w : WittVector p R) :
    HasSubst (fun k => subst (frobPolyFam p R) (mulFam p w k)) :=
  hasSubst_subst_comp (hasSubst_mulFam w) hasSubst_frobPolyFam


public theorem subst_verFam_mulFam_frobPolyFam (w : WittVector p R) (n : ℕ) :
    subst (fun k => subst (frobPolyFam p R) (mulFam p w k)) (verFam R n) =
      mulFam p (WittVector.verschiebung w) n := by
  have hc := hasSubst_mulFam_frobPolyFam (p := p) (R := R) w
  cases n with
  | zero =>
    rw [verFam_zero, ← coe_substAlgHom hc, map_zero, mulFam_apply, mulPoly_verschiebung_zero,
      MvPolynomial.coe_zero]
  | succ k =>
    rw [verFam_succ, subst_X hc, subst_frobPolyFam_mulFam, mulFam_apply, mulPoly_verschiebung_succ]

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R] {Φ : MvFormalGroup d R}


public theorem verschiebungInt_smul_frobenius [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) :
    verschiebungInt (w • frobenius f) = WittVector.verschiebung w • f := by
  apply CartierModule.ext
  funext j
  show subst (WittLaw.frobPolyFam p R) (subst (WittLaw.mulFam p w)
      (subst (WittLaw.verFam R) (f.toPowerSeries j))) =
    subst (WittLaw.mulFam p (WittVector.verschiebung w)) (f.toPowerSeries j)
  rw [subst_comp_subst_apply (WittLaw.hasSubst_mulFam w) WittLaw.hasSubst_frobPolyFam,
    subst_comp_subst_apply WittLaw.hasSubst_verFam (WittLaw.hasSubst_mulFam_frobPolyFam w)]
  congr 1
  funext n
  exact WittLaw.subst_verFam_mulFam_frobPolyFam w n

end CartierModule

end MvFormalGroup

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvPowerSeries.CartierModule MvPowerSeries PowerSeries MvPolynomial

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]


public theorem endAct_varpiEnd_endAct_varpiEnd (X : FormalODModule p B) (f : CartierModule p X.F) :
    endAct X.varpiEnd (endAct X.varpiEnd f) = (p : ℕ) • f := by
  have h : endAct (p := p) X.varpiEnd * endAct (p := p) X.varpiEnd =
      endAct (p := p) ((p : ℕ) : MvFormalGroup.End X.F) := by
    rw [← map_mul, varpiEnd_mul_varpiEnd, map_natCast]
  rw [← endAct_natCast p f, ← h]
  rfl


@[simp] public theorem varpiLinear_apply (X : FormalODModule p B) (f : CartierModule p X.F) :
    X.varpiLinear f = endAct X.varpiEnd f := rfl


public theorem smul_mem_gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (w : WittVector p B) (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) :
    w • f ∈ X.gradedPiece j n := by
  refine (mem_gradedPiece_iff X j n _).2 fun c => ?_
  rw [endAct_smul_witt, homothety_smul_witt, (mem_gradedPiece_iff X j n f).1 hf c]


@[simp] public theorem mem_gradedSubmodule_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) : f ∈ X.gradedSubmodule j n ↔ f ∈ X.gradedPiece j n :=
  Iff.rfl


@[simp] public theorem gradedSubmodule_toAddSubgroup (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    (X.gradedSubmodule j n).toAddSubgroup = X.gradedPiece j n :=
  rfl


public theorem gradedSubmodule_add_two (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    X.gradedSubmodule j (n + 2) = X.gradedSubmodule j n :=
  Submodule.toAddSubgroup_injective (by
    rw [gradedSubmodule_toAddSubgroup, gradedSubmodule_toAddSubgroup, gradedPiece_add_two])


public theorem isCompl_gradedSubmodule_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (m n : ℕ) :
    IsCompl (X.gradedSubmodule j m) (X.gradedSubmodule j n) ↔
      IsCompl (X.gradedPiece j m) (X.gradedPiece j n) := by
  simp only [isCompl_iff, disjoint_iff_inf_le, codisjoint_iff_le_sup, SetLike.le_def,
    Submodule.mem_inf, AddSubgroup.mem_inf, Submodule.mem_bot, AddSubgroup.mem_bot,
    Submodule.mem_top, AddSubgroup.mem_top, Submodule.mem_sup, AddSubgroup.mem_sup,
    mem_gradedSubmodule_iff]


public theorem gradedPiece_fin_add_one (X : FormalODModule p B) (j : Zp2 p →+* B) (i : Fin 2) :
    X.gradedPiece j ((i + 1 : Fin 2) : ℕ) = X.gradedPiece j ((i : ℕ) + 1) := by
  fin_cases i
  · rfl
  · exact (gradedPiece_add_two X j 0).symm


public theorem verschiebungInt_mem_gradedPiece_succ (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) :
    verschiebungInt f ∈ X.gradedPiece j (n + 1) := by
  refine (mem_gradedPiece_iff X j (n + 1) _).2 fun c => ?_
  have h2 : j (WittVector.teichmuller p c) ^ p ^ (n + 1 + 1) =
      j (WittVector.teichmuller p c) ^ p ^ n :=
    apply_teichmuller_pow_pow_add_two j c n
  rw [endAct_verschiebungInt, (mem_gradedPiece_iff X j n f).1 hf c, homothety_verschiebungInt,
    ← pow_mul, ← pow_succ, h2]


public theorem frobenius_mem_gradedPiece_succ (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) :
    frobenius f ∈ X.gradedPiece j (n + 1) := by
  refine (mem_gradedPiece_iff X j (n + 1) _).2 fun c => ?_
  rw [endAct_frobenius, (mem_gradedPiece_iff X j n f).1 hf c, frobenius_homothety, ← pow_mul,
    ← pow_succ]


public theorem endAct_varpiEnd_mem_gradedPiece_succ (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) :
    endAct X.varpiEnd f ∈ X.gradedPiece j (n + 1) := by
  refine (mem_gradedPiece_iff X j (n + 1) _).2 fun c => ?_
  have hc : WittVector.teichmuller p c =
      WittVector.frobenius (WittVector.teichmuller p (c ^ p)) := by
    rw [WittVector.frobenius_teichmuller_eq, ← pow_mul, ← pow_two, pow_card_galoisField]
  have key : endAct (X.actEnd (WittVector.teichmuller p c)) (endAct X.varpiEnd f) =
      endAct X.varpiEnd (endAct (X.actEnd (WittVector.teichmuller p (c ^ p))) f) := by
    show (endAct (p := p) (X.actEnd (WittVector.teichmuller p c)) * endAct (p := p) X.varpiEnd) f =
      (endAct (p := p) X.varpiEnd *
        endAct (p := p) (X.actEnd (WittVector.teichmuller p (c ^ p)))) f
    rw [← map_mul, ← map_mul, hc, ← varpiEnd_mul_actEnd]
  rw [key, (mem_gradedPiece_iff X j n f).1 hf (c ^ p), endAct_homothety,
    map_pow (WittVector.teichmuller p) c p, map_pow j _ p, ← pow_mul, ← pow_succ']


public theorem toGradedCartierModuleData_M :
    (X.toGradedCartierModuleData j hc).M = CartierModule p X.F := rfl


public theorem toGradedCartierModuleData_frobenius :
    (X.toGradedCartierModuleData j hc).frobenius = MvPowerSeries.CartierModule.frobenius := rfl


@[simp] public theorem toGradedCartierModuleData_frobenius_apply (f : CartierModule p X.F) :
    (X.toGradedCartierModuleData j hc).frobenius f = MvPowerSeries.CartierModule.frobenius f := rfl


public theorem toGradedCartierModuleData_verschiebung :
    (X.toGradedCartierModuleData j hc).verschiebung = MvFormalGroup.CartierModule.verschiebungInt :=
  rfl


@[simp] public theorem toGradedCartierModuleData_verschiebung_apply (f : CartierModule p X.F) :
    (X.toGradedCartierModuleData j hc).verschiebung f = verschiebungInt f := rfl


public theorem toGradedCartierModuleData_varpi :
    (X.toGradedCartierModuleData j hc).varpi = X.varpiLinear := rfl


@[simp] public theorem toGradedCartierModuleData_varpi_apply (f : CartierModule p X.F) :
    (X.toGradedCartierModuleData j hc).varpi f = endAct X.varpiEnd f := rfl


public theorem toGradedCartierModuleData_piece (i : Fin 2) :
    (X.toGradedCartierModuleData j hc).piece i = X.gradedSubmodule j (i : ℕ) := rfl


@[simp] public theorem mem_toGradedCartierModuleData_piece_iff (i : Fin 2) (f : CartierModule p X.F) :
    f ∈ (X.toGradedCartierModuleData j hc).piece i ↔ f ∈ X.gradedPiece j (i : ℕ) := Iff.rfl


public theorem toGradedCartierModuleData_smul (w : WittVector p B) (f : CartierModule p X.F) :
    (HSMul.hSMul (γ := (X.toGradedCartierModuleData j hc).M) w f) = w • f := rfl


@[simp high] public theorem toGradedCartierModuleData_homothety_apply (b : B) (f : CartierModule p X.F) :
    (X.toGradedCartierModuleData j hc).homothety b f = homothety b f :=
  teichmuller_smul b f

end model

end FormalODModule

end CerednikDrinfeld

end
