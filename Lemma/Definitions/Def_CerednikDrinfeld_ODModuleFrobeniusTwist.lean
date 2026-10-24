import Mathlib
import Lemma.Definitions.Def_MvFormalGroup_NegV2
import Lemma.Definitions.Def_MvFormalGroup_CartierModule
import Lemma.Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Lemma.Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Lemma.Definitions.Def_CerednikDrinfeld_CartierGradedPiece

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld

variable {p : ℕ} [hp : Fact p.Prime]

namespace Zp2

theorem frobenius_frobenius (a : Zp2 p) :
    WittVector.frobenius (WittVector.frobenius a) = a := by
  ext n
  haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul]
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 two_ne_zero
  have : p * p = Fintype.card (GaloisField p 2) := by rw [hcard, pow_two]
  rw [this, FiniteField.pow_card]

theorem frobenius_bijective :
    Function.Bijective (WittVector.frobenius : Zp2 p → Zp2 p) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨WittVector.frobenius, frobenius_frobenius, frobenius_frobenius⟩

theorem frobenius_comp_frobenius :
    (WittVector.frobenius : Zp2 p →+* Zp2 p).comp WittVector.frobenius = RingHom.id _ :=
  RingHom.ext frobenius_frobenius

theorem frobenius_teichmuller (c : GaloisField p 2) :
    WittVector.frobenius (WittVector.teichmuller p c) = WittVector.teichmuller p (c ^ p) := by
  ext n
  rw [WittVector.coeff_frobenius_charP]
  cases n with
  | zero => rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  | succ n =>
    rw [WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n),
      WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n), zero_pow hp.out.ne_zero]

theorem iterate_frobenius_teichmuller (m : ℕ) (c : GaloisField p 2) :
    (WittVector.frobenius : Zp2 p → Zp2 p)^[m] (WittVector.teichmuller p c) =
      WittVector.teichmuller p (c ^ p ^ m) := by
  induction m with
  | zero => rw [Function.iterate_zero, id, pow_zero, pow_one]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, frobenius_teichmuller, ← pow_mul, ← pow_succ]

theorem pow_frobenius_apply (m : ℕ) (a : Zp2 p) :
    ((WittVector.frobenius : Zp2 p →+* Zp2 p) ^ m) a = (WittVector.frobenius : Zp2 p → Zp2 p)^[m] a := by
  rw [RingHom.coe_pow]

end Zp2

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule SpecialFormal

variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']

def frobTwist (X : FormalODModule p B) : FormalODModule p B where
  F := X.F
  isComm := X.isComm
  act a := X.act (WittVector.frobenius a)
  varpi := X.varpi
  isLawHom_act a := X.isLawHom_act _
  isLawHom_varpi := X.isLawHom_varpi
  act_one := by rw [map_one, X.act_one]
  act_mul a b := by rw [map_mul, X.act_mul]
  act_add a b := by rw [map_add, X.act_add]
  varpi_comp_varpi := by rw [X.varpi_comp_varpi, map_natCast]
  varpi_comp_act a := X.varpi_comp_act _

@[simp] theorem frobTwist_F (X : FormalODModule p B) : (frobTwist X).F = X.F := rfl
@[simp] theorem frobTwist_act (X : FormalODModule p B) (a : Zp2 p) :
    (frobTwist X).act a = X.act (WittVector.frobenius a) := rfl
@[simp] theorem frobTwist_varpi (X : FormalODModule p B) : (frobTwist X).varpi = X.varpi := rfl

@[simp] theorem frobTwist_frobTwist (X : FormalODModule p B) : frobTwist (frobTwist X) = X :=
  ext' rfl (funext fun a => by rw [frobTwist_act, frobTwist_act, Zp2.frobenius_frobenius]) rfl

theorem eq_frobTwist {X X' : FormalODModule p B} (hF : X'.F = X.F) (hvarpi : X'.varpi = X.varpi)
    (hact : ∀ a, X'.act a = X.act (WittVector.frobenius a)) : X' = frobTwist X :=
  ext' hF (funext hact) hvarpi

theorem frobTwist_eq_iff (X X' : FormalODModule p B) :
    X' = frobTwist X ↔ X'.F = X.F ∧ X'.varpi = X.varpi ∧ ∀ a, X'.act a = X.act (WittVector.frobenius a) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, fun _ => rfl⟩
  · rintro ⟨hF, hv, ha⟩
    exact eq_frobTwist hF hv ha

theorem frobTwist_map (X : FormalODModule p B) (f : B →+* B') :
    (frobTwist X).map f = frobTwist (X.map f) :=
  ext' rfl rfl rfl

theorem actEnd_frobTwist (X : FormalODModule p B) (a : Zp2 p) :
    (frobTwist X).actEnd a = X.actEnd (WittVector.frobenius a) :=
  MvFormalGroup.Hom.ext rfl

theorem varpiEnd_frobTwist (X : FormalODModule p B) : (frobTwist X).varpiEnd = X.varpiEnd := rfl

theorem range_actEnd_frobTwist (X : FormalODModule p B) :
    Set.range (frobTwist X).actEnd = Set.range X.actEnd := by
  ext e
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨WittVector.frobenius a, (actEnd_frobTwist X a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨WittVector.frobenius a, ?_⟩
    rw [actEnd_frobTwist, Zp2.frobenius_frobenius]

theorem IsODHom.frobTwist {X Y : FormalODModule p B} {φ : Series B} (h : IsODHom X Y φ) :
    IsODHom (frobTwist X) (frobTwist Y) φ :=
  ⟨h.1, fun a => h.2.1 (WittVector.frobenius a), h.2.2⟩

theorem isODHom_frobTwist_iff {X Y : FormalODModule p B} {φ : Series B} :
    IsODHom (frobTwist X) (frobTwist Y) φ ↔ IsODHom X Y φ := by
  refine ⟨fun h => ?_, IsODHom.frobTwist⟩
  have h' := h.frobTwist
  rwa [frobTwist_frobTwist, frobTwist_frobTwist] at h'

theorem isODHom_varpi_frobTwist (X : FormalODModule p B) : IsODHom X (frobTwist X) X.varpi :=
  ⟨X.isLawHom_varpi, fun a => X.varpi_comp_act a, rfl⟩

theorem isODHom_varpi_frobTwist' (X : FormalODModule p B) : IsODHom (frobTwist X) X X.varpi := by
  refine ⟨X.isLawHom_varpi, fun a => ?_, rfl⟩
  show X.varpi.comp (X.act (WittVector.frobenius a)) = (X.act a).comp X.varpi
  rw [X.varpi_comp_act, Zp2.frobenius_frobenius]

theorem lieAct_frobTwist (X : FormalODModule p B) (a : Zp2 p) :
    (frobTwist X).lieAct a = X.lieAct (WittVector.frobenius a) := rfl

theorem lieZero_comp_frobenius (X : FormalODModule p B) (j : Zp2 p →+* B) :
    X.lieZero (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) = X.lieOne j := rfl

theorem lieOne_comp_frobenius (X : FormalODModule p B) (j : Zp2 p →+* B) :
    X.lieOne (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) = X.lieZero j := by
  unfold lieOne lieZero
  simp only [RingHom.comp_apply, Zp2.frobenius_frobenius]

theorem isSpecial_comp_frobenius_iff (X : FormalODModule p B) (j : Zp2 p →+* B) :
    X.IsSpecial (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) ↔ X.IsSpecial j := by
  unfold IsSpecial
  rw [lieZero_comp_frobenius, lieOne_comp_frobenius]
  exact ⟨fun h => ⟨h.1.symm, h.2.2, h.2.1⟩, fun h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩

theorem lieZero_frobTwist (X : FormalODModule p B) (j : Zp2 p →+* B) :
    (frobTwist X).lieZero (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) = X.lieZero j := by
  apply le_antisymm
  · refine le_iInf fun b => ?_
    obtain ⟨a, rfl⟩ := (Zp2.frobenius_bijective (p := p)).2 b
    exact iInf_le _ a
  · exact le_iInf fun a => iInf_le _ (WittVector.frobenius a)

theorem lieOne_frobTwist (X : FormalODModule p B) (j : Zp2 p →+* B) :
    (frobTwist X).lieOne (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) = X.lieOne j := by
  apply le_antisymm
  · refine le_iInf fun b => ?_
    obtain ⟨a, rfl⟩ := (Zp2.frobenius_bijective (p := p)).2 b
    refine (iInf_le _ a).trans (le_of_eq ?_)
    simp only [lieAct_frobTwist, RingHom.comp_apply, Zp2.frobenius_frobenius]
  · refine le_iInf fun a => (iInf_le _ (WittVector.frobenius a)).trans (le_of_eq ?_)
    simp only [lieAct_frobTwist, RingHom.comp_apply, Zp2.frobenius_frobenius]

theorem lieZero_frobTwist_self (X : FormalODModule p B) (j : Zp2 p →+* B) :
    (frobTwist X).lieZero j = X.lieOne j := by
  have h := lieZero_frobTwist X (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p))
  rw [RingHom.comp_assoc, Zp2.frobenius_comp_frobenius, RingHom.comp_id] at h
  rw [h, lieZero_comp_frobenius]

theorem lieOne_frobTwist_self (X : FormalODModule p B) (j : Zp2 p →+* B) :
    (frobTwist X).lieOne j = X.lieZero j := by
  have h := lieOne_frobTwist X (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p))
  rw [RingHom.comp_assoc, Zp2.frobenius_comp_frobenius, RingHom.comp_id] at h
  rw [h, lieOne_comp_frobenius]

theorem isSpecial_frobTwist_iff (X : FormalODModule p B) (j : Zp2 p →+* B) :
    (frobTwist X).IsSpecial (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) ↔ X.IsSpecial j := by
  unfold IsSpecial
  rw [lieZero_frobTwist, lieOne_frobTwist]

theorem isSpecial_frobTwist_self_iff (X : FormalODModule p B) (j : Zp2 p →+* B) :
    (frobTwist X).IsSpecial j ↔ X.IsSpecial j := by
  rw [← isSpecial_comp_frobenius_iff (frobTwist X) j, isSpecial_frobTwist_iff]

theorem hasHeight_frobTwist_iff (X : FormalODModule p B) (h : ℕ) :
    (frobTwist X).HasHeight h ↔ X.HasHeight h := by
  unfold HasHeight
  rw [frobTwist_act, map_natCast]

theorem gradedPiece_comp_frobenius (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    X.gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) n = X.gradedPiece j (n + 1) := by
  ext f
  simp only [mem_gradedPiece_iff, RingHom.comp_apply, Zp2.frobenius_teichmuller, map_pow, ← pow_mul]
  constructor <;> intro h c <;> specialize h c
  · rwa [pow_succ, mul_comm]
  · rwa [pow_succ, mul_comm] at h

theorem gradedPiece_comp_frobenius_pow (X : FormalODModule p B) (j : Zp2 p →+* B) (m n : ℕ) :
    X.gradedPiece (j.comp ((WittVector.frobenius : Zp2 p →+* Zp2 p) ^ m)) n = X.gradedPiece j (n + m) := by
  induction m generalizing j with
  | zero => rw [pow_zero, add_zero]; rfl
  | succ m ih =>
    rw [pow_succ', RingHom.mul_def, ← RingHom.comp_assoc, ih, gradedPiece_comp_frobenius, add_assoc]

theorem gradedPiece_frobTwist (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    (frobTwist X).gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) n = X.gradedPiece j n := by
  ext f
  simp only [mem_gradedPiece_iff, RingHom.comp_apply, actEnd_frobTwist, Zp2.frobenius_teichmuller]
  constructor <;> intro h c
  ·
    have hc : (c ^ p) ^ p = c := by rw [← pow_mul, ← pow_two, pow_card_galoisField]
    have := h (c ^ p)
    rwa [hc] at this
  · exact h (c ^ p)

theorem gradedPiece_frobTwist_self (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    (frobTwist X).gradedPiece j n = X.gradedPiece j (n + 1) := by
  have h := gradedPiece_frobTwist X (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) n
  rw [RingHom.comp_assoc, Zp2.frobenius_comp_frobenius, RingHom.comp_id] at h
  rw [h, gradedPiece_comp_frobenius]

end FormalODModule

end CerednikDrinfeld

end
