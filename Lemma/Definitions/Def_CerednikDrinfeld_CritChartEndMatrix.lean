import Mathlib
import Lemma.Definitions.Def_MvFormalGroup_NegV2
import Lemma.Definitions.Def_MvFormalGroup_CartierModule
import Lemma.Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Lemma.Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Lemma.Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Lemma.Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Lemma.Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Lemma.Definitions.Def_CerednikDrinfeld_CriticalIndexChart

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace CartierModule

variable (p : ℕ) [hp : Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]

def padicIntToWitt : ℤ_[p] →+* WittVector p R :=
  (WittVector.map (ZMod.castHom (dvd_refl p) R)).comp (WittVector.equiv p).symm.toRingHom

theorem padicIntToWitt_apply (z : ℤ_[p]) :
    padicIntToWitt p R z = WittVector.map (ZMod.castHom (dvd_refl p) R) ((WittVector.equiv p).symm z) :=
  rfl

theorem frobenius_padicIntToWitt (z : ℤ_[p]) :
    WittVector.frobenius (padicIntToWitt p R z) = padicIntToWitt p R z := by
  rw [padicIntToWitt_apply]
  set w := (WittVector.equiv p).symm z
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.map_coeff, ← map_pow, ZMod.pow_card]

theorem padicIntToWitt_injective [Nontrivial R] : Function.Injective (padicIntToWitt p R) :=
  (WittVector.map_injective _ (ZMod.castHom (dvd_refl p) R).injective).comp
    (WittVector.equiv p).symm.injective

theorem padicIntToWitt_natCast (n : ℕ) : padicIntToWitt p R n = n := map_natCast _ n

variable {p R}
variable {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

instance instModulePadicInt : Module ℤ_[p] (CartierModule p Φ) :=
  Module.compHom (CartierModule p Φ) (padicIntToWitt p R)

theorem padicInt_smul_def (z : ℤ_[p]) (f : CartierModule p Φ) : z • f = padicIntToWitt p R z • f := rfl

theorem map_smul_padicInt {d' : ℕ} {Φ' : MvFormalGroup d' R} [Φ'.IsComm] (φ : Φ.Hom Φ') (z : ℤ_[p])
    (f : CartierModule p Φ) : map φ (z • f) = z • map φ f := by
  rw [padicInt_smul_def, padicInt_smul_def, map_smul_witt]

theorem endAct_smul_padicInt (φ : MvFormalGroup.End Φ) (z : ℤ_[p]) (f : CartierModule p Φ) :
    endAct φ (z • f) = z • endAct φ f :=
  map_smul_padicInt φ z f

theorem verschiebung_smul_padicInt (z : ℤ_[p]) (f : CartierModule p Φ) :
    verschiebung (z • f) = z • verschiebung f := by
  rw [padicInt_smul_def, padicInt_smul_def, smul_verschiebung, frobenius_padicIntToWitt]

theorem frobenius_smul_padicInt (z : ℤ_[p]) (f : CartierModule p Φ) :
    frobenius (z • f) = z • frobenius f := by
  rw [padicInt_smul_def, padicInt_smul_def, frobenius_smul, frobenius_padicIntToWitt]

theorem homothety_smul_padicInt (a : R) (z : ℤ_[p]) (f : CartierModule p Φ) :
    homothety a (z • f) = z • homothety a f := by
  rw [padicInt_smul_def, padicInt_smul_def, homothety_smul_witt]

theorem smul_verschiebung_of_frobenius_eq {w : WittVector p R} (hw : WittVector.frobenius w = w)
    (f : CartierModule p Φ) : w • verschiebung f = verschiebung (w • f) := by
  rw [smul_verschiebung, hw]

end CartierModule

end MvFormalGroup

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

abbrev endOD (X : FormalODModule p B) : Subring (MvFormalGroup.End X.F) :=
  Subring.centralizer (Set.range X.actEnd ∪ {X.varpiEnd})

theorem mem_endOD_iff (X : FormalODModule p B) (f : MvFormalGroup.End X.F) :
    f ∈ endOD X ↔ (∀ a, X.actEnd a * f = f * X.actEnd a) ∧ X.varpiEnd * f = f * X.varpiEnd := by
  rw [endOD, Subring.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun a => h _ (Or.inl ⟨a, rfl⟩), h _ (Or.inr rfl)⟩
  · rintro ⟨ha, hv⟩ g (⟨a, rfl⟩ | hg)
    · exact ha a
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hv

theorem endAct_actEnd_comm {X : FormalODModule p B} {f : MvFormalGroup.End X.F} (hf : f ∈ endOD X)
    (a : Zp2 p) (m : CartierModule p X.F) :
    endAct f (endAct (X.actEnd a) m) = endAct (X.actEnd a) (endAct f m) := by
  show (endAct f * endAct (X.actEnd a) : AddMonoid.End (CartierModule p X.F)) m =
    (endAct (X.actEnd a) * endAct f : AddMonoid.End (CartierModule p X.F)) m
  rw [← map_mul, ← map_mul, ((mem_endOD_iff X f).1 hf).1 a]

theorem endAct_varpiEnd_comm {X : FormalODModule p B} {f : MvFormalGroup.End X.F} (hf : f ∈ endOD X)
    (m : CartierModule p X.F) :
    endAct f (endAct X.varpiEnd m) = endAct X.varpiEnd (endAct f m) := by
  show (endAct f * endAct X.varpiEnd : AddMonoid.End (CartierModule p X.F)) m =
    (endAct X.varpiEnd * endAct f : AddMonoid.End (CartierModule p X.F)) m
  rw [← map_mul, ← map_mul, ((mem_endOD_iff X f).1 hf).2]

theorem endAct_mem_gradedPiece {X : FormalODModule p B} (j : Zp2 p →+* B) {f : MvFormalGroup.End X.F}
    (hf : f ∈ endOD X) (n : ℕ) {m : CartierModule p X.F} (hm : m ∈ X.gradedPiece j n) :
    endAct f m ∈ X.gradedPiece j n := fun c => by
  rw [← endAct_actEnd_comm hf, hm c, endAct_homothety]

variable [CharP B p]

theorem verschiebung_mem_gradedPiece_succ {X : FormalODModule p B} (j : Zp2 p →+* B) (n : ℕ)
    {m : CartierModule p X.F} (hm : m ∈ X.gradedPiece j n) :
    verschiebung m ∈ X.gradedPiece j (n + 1) := fun c => by
  rw [endAct_verschiebung, hm c, homothety_verschiebung, ← pow_mul, ← pow_succ,
    apply_teichmuller_pow_pow_add_two j c n]

theorem endAct_mem_invariants {X : FormalODModule p B} (j : Zp2 p →+* B) {f : MvFormalGroup.End X.F}
    (hf : f ∈ endOD X) (i : ℕ) {m : CartierModule p X.F} (hm : m ∈ CritChart.invariants X j i) :
    endAct f m ∈ CritChart.invariants X j i :=
  ⟨endAct_mem_gradedPiece j hf i hm.1, by rw [← endAct_varpiEnd_comm hf, hm.2, endAct_verschiebung]⟩

theorem smul_witt_mem_invariants_of_frobenius_eq {X : FormalODModule p B} (j : Zp2 p →+* B) (i : ℕ)
    {w : WittVector p B} (hw : WittVector.frobenius w = w) {m : CartierModule p X.F}
    (hm : m ∈ CritChart.invariants X j i) : w • m ∈ CritChart.invariants X j i := by
  refine ⟨fun c => ?_, ?_⟩
  · rw [endAct_smul_witt, hm.1 c, homothety_smul_witt]
  · rw [endAct_smul_witt, hm.2, smul_verschiebung_of_frobenius_eq hw]

theorem smul_padicInt_mem_invariants {X : FormalODModule p B} (j : Zp2 p →+* B) (i : ℕ) (z : ℤ_[p])
    {m : CartierModule p X.F} (hm : m ∈ CritChart.invariants X j i) : z • m ∈ CritChart.invariants X j i :=
  smul_witt_mem_invariants_of_frobenius_eq j i (frobenius_padicIntToWitt p B z) hm

namespace CritChart

def invariantsSubmodule (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    Submodule ℤ_[p] (CartierModule p X.F) where
  carrier := invariants X j i
  zero_mem' := zero_mem _
  add_mem' := add_mem
  smul_mem' z _ hm := smul_padicInt_mem_invariants j i z hm

@[simp] theorem mem_invariantsSubmodule_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (m : CartierModule p X.F) : m ∈ invariantsSubmodule X j i ↔ m ∈ invariants X j i :=
  Iff.rfl

theorem coe_invariantsSubmodule (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    (invariantsSubmodule X j i : Set (CartierModule p X.F)) = invariants X j i := rfl

def endODInvariantsLin (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) (f : endOD X) :
    Module.End ℤ_[p] (invariantsSubmodule X j i) where
  toFun m := ⟨endAct (f : MvFormalGroup.End X.F) m, endAct_mem_invariants j f.2 i m.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' z _ := Subtype.ext (endAct_smul_padicInt _ z _)

@[simp] theorem coe_endODInvariantsLin_apply (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (f : endOD X) (m : invariantsSubmodule X j i) :
    (endODInvariantsLin X j i f m : CartierModule p X.F) = endAct (f : MvFormalGroup.End X.F) m := rfl

def endODInvariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    endOD X →+* Module.End ℤ_[p] (invariantsSubmodule X j i) where
  toFun := endODInvariantsLin X j i
  map_one' := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, OneMemClass.coe_one, map_one]; rfl)
  map_mul' f g := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, Subring.coe_mul, map_mul]; rfl)
  map_zero' := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, ZeroMemClass.coe_zero, map_zero]; rfl)
  map_add' f g := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, Subring.coe_add, map_add]; rfl)

@[simp] theorem coe_endODInvariants_apply (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (f : endOD X) (m : invariantsSubmodule X j i) :
    (endODInvariants X j i f m : CartierModule p X.F) = endAct (f : MvFormalGroup.End X.F) m := rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def endMatrix (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) : endOD X →+* Matrix ι ι ℤ_[p] :=
  (LinearMap.toMatrixAlgEquiv β).toRingEquiv.toRingHom.comp (endODInvariants X j i)

theorem endMatrix_apply (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) (f : endOD X) :
    endMatrix X j i β f = LinearMap.toMatrix β β (endODInvariants X j i f) := rfl

theorem endMatrix_apply_eq_repr (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) (f : endOD X) (r s : ι) :
    endMatrix X j i β f r s = β.repr (endODInvariants X j i f (β s)) r := by
  rw [endMatrix_apply, LinearMap.toMatrix_apply]

theorem sum_endMatrix_smul (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) (f : endOD X) (s : ι) :
    ∑ r, endMatrix X j i β f r s • β r = endODInvariants X j i f (β s) := by
  simp_rw [endMatrix_apply_eq_repr]
  exact β.sum_repr _

def endMatrixQ (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) : endOD X →+* Matrix ι ι ℚ_[p] :=
  (algebraMap ℤ_[p] ℚ_[p]).mapMatrix.comp (endMatrix X j i β)

theorem endMatrixQ_apply (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) (f : endOD X) :
    endMatrixQ X j i β f = (endMatrix X j i β f).map ((↑) : ℤ_[p] → ℚ_[p]) := rfl

end CritChart

end FormalODModule

end CerednikDrinfeld

end
