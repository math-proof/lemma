module

public import Mathlib
public import Def.FormalGroup_NegV2
public import Def.FormalGroup_CartierModule
public import Def.PowerSeries_CartierModuleHomothety
public import Def.FormalGroup_CartierModuleWittAction
public import Structure.MvFormalGroup_WittPointFamily

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace MvFormalGroup

open MvPowerSeries WittLaw


namespace SeriesPoint

variable {d d' : ℕ} {R : Type u} [CommRing R] {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}
  {τ : Type v} {τ' : Type w}

protected def zero : SeriesPoint Φ τ := ⟨fun _ => 0, fun _ => map_zero _⟩

protected def add (a b : SeriesPoint Φ τ) : SeriesPoint Φ τ where
  val := fun j => subst (Sum.elim a.val b.val) (Φ.toPowerSeries j)
  constantCoeff_eq_zero := constantCoeff_subst_elim Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero

protected def neg (a : SeriesPoint Φ τ) : SeriesPoint Φ τ where
  val := negSeries Φ a.val
  constantCoeff_eq_zero := constantCoeff_negSeries Φ a.val

def mapPt [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') : SeriesPoint Φ τ →+ SeriesPoint Φ' τ where
  toFun a := ⟨fun i => subst a.val (φ.toPowerSeries i), fun i =>
    constantCoeff_subst_eq_zero a.hasSubst_val a.constantCoeff_eq_zero (φ.constantCoeff_eq_zero i)⟩
  map_zero' := SeriesPoint.ext (funext fun i =>
    subst_zero_of_constantCoeff_eq_zero (φ.constantCoeff_eq_zero i))
  map_add' a b := SeriesPoint.ext (funext fun i =>
    φ.subst_subst_elim a.constantCoeff_eq_zero b.constantCoeff_eq_zero i)

def substPt [Φ.IsComm] {b : τ → MvPowerSeries τ' R} (hb : HasSubst b)
    (hb0 : ∀ t, (b t).constantCoeff = 0) : SeriesPoint Φ τ →+ SeriesPoint Φ τ' where
  toFun a := ⟨fun j => subst b (a.val j), fun j =>
    constantCoeff_subst_eq_zero hb hb0 (a.constantCoeff_eq_zero j)⟩
  map_zero' := SeriesPoint.ext (funext fun j => by
    show subst b (0 : MvPowerSeries τ R) = 0
    rw [← coe_substAlgHom hb, map_zero])
  map_add' a c := SeriesPoint.ext (funext fun j =>
    subst_subst_elim Φ a.constantCoeff_eq_zero c.constantCoeff_eq_zero hb j)

end SeriesPoint

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R] {τ : Type v} {τ' : Type w}

def pairSeries (a b : ℕ → MvPowerSeries τ R) : Fin 2 × ℕ → MvPowerSeries τ R :=
  fun im => Fin.cases (a im.2) (fun _ => b im.2) im.1

variable {p}

omit hp [CommRing R] in
variable (p R τ)

def seriesPoint : AddSubgroup (WittVector p (MvPowerSeries τ R)) where
  carrier := {x | (∀ n, (x.coeff n).constantCoeff = 0) ∧ HasSubst (fun n => x.coeff n)}
  zero_mem' := ⟨fun n => by rw [WittVector.zero_coeff, map_zero], by
    simpa only [WittVector.zero_coeff] using (HasSubst.zero : HasSubst fun _ : ℕ => (0 : MvPowerSeries τ R))⟩
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    have hP := hasSubst_pairSeries hx hy
    have hfam : (fun n => (x + y).coeff n) = fun n => subst (pairSeries x.coeff y.coeff) (addFam p R n) :=
      funext (add_coeff_eq_subst_addFam x y)
    refine ⟨fun n => ?_, ?_⟩
    · rw [add_coeff_eq_subst_addFam]
      exact constantCoeff_subst_eq_zero hP (constantCoeff_pairSeries hx0 hy0) (constantCoeff_addFam p R n)
    · rw [hfam]
      simpa only [coe_substAlgHom] using (hasSubst_addFam p R).comp hP
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    have hneg : -x = WittVector.map (C : R →+* MvPowerSeries τ R) (-1) * x := by
      rw [map_neg, map_one, neg_one_mul]
    have hfam : (fun n => (-x).coeff n) = fun n => subst x.coeff (mulFam p (-1 : WittVector p R) n) := by
      funext n
      rw [hneg, map_C_mul_coeff_eq_subst_mulFam]
    refine ⟨fun n => ?_, ?_⟩
    · rw [hneg, map_C_mul_coeff_eq_subst_mulFam]
      exact constantCoeff_subst_eq_zero hx hx0 (constantCoeff_mulFam _ n)
    · rw [hfam]
      simpa only [coe_substAlgHom] using (hasSubst_mulFam (-1 : WittVector p R)).comp hx

variable {p R τ}

def wittSMulPt (w : WittVector p R) : seriesPoint p R τ →+ seriesPoint p R τ where
  toFun x := ⟨WittVector.map (C : R →+* MvPowerSeries τ R) w * x, map_C_mul_mem w x.2⟩
  map_zero' := Subtype.ext (mul_zero _)
  map_add' _ _ := Subtype.ext (mul_add _ _ _)

def teichPt (c : R) : seriesPoint p R τ →+ seriesPoint p R τ :=
  wittSMulPt (WittVector.teichmuller p c)

def verPt : seriesPoint p R τ →+ seriesPoint p R τ where
  toFun x := ⟨WittVector.verschiebung x, verschiebung_mem x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def frobPt [CharP R p] : seriesPoint p R τ →+ seriesPoint p R τ where
  toFun x := ⟨WittVector.frobenius x, frobenius_mem x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def tautPt : seriesPoint p R ℕ :=
  ⟨WittVector.mk p fun n => (X n : MvPowerSeries ℕ R), fun n => by
    rw [WittVector.coeff_mk, constantCoeff_X], by simpa only [WittVector.coeff_mk] using HasSubst.X⟩

def curveTautPt : seriesPoint p R Unit :=
  ⟨WittVector.mk p (CartierModule.curveFam R), fun n => by
    rw [WittVector.coeff_mk]; exact CartierModule.constantCoeff_curveFam n, by
    simpa only [WittVector.coeff_mk] using (CartierModule.hasSubst_curveFam (R := R))⟩

def substPt {b : τ → MvPowerSeries τ' R} (hb : HasSubst b) (hb0 : ∀ t, (b t).constantCoeff = 0) :
    seriesPoint p R τ →+ seriesPoint p R τ' where
  toFun x := ⟨WittVector.mk p fun n => subst b ((x : WittVector p (MvPowerSeries τ R)).coeff n),
    map_subst_mem hb hb0 x.2⟩
  map_zero' := Subtype.ext (WittVector.ext fun n => by
    change subst b (((0 : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n) =
      ((0 : seriesPoint p R τ') : WittVector p (MvPowerSeries τ' R)).coeff n
    rw [AddSubgroup.coe_zero, WittVector.zero_coeff, AddSubgroup.coe_zero, WittVector.zero_coeff,
      ← coe_substAlgHom hb, map_zero])
  map_add' x y := Subtype.ext (WittVector.ext fun n => by
    change subst b (((x + y : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n) =
      ((⟨_, map_subst_mem hb hb0 x.2⟩ + ⟨_, map_subst_mem hb hb0 y.2⟩ : seriesPoint p R τ') :
        WittVector p (MvPowerSeries τ' R)).coeff n
    rw [coe_add_coeff, coe_add_coeff, subst_comp_subst_apply
      (hasSubst_pairSeries (hasSubst_coeff x) (hasSubst_coeff y)) hb]
    congr 1
    funext ⟨i, m⟩
    refine Fin.cases rfl (fun l => ?_) i
    fin_cases l; rfl)

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {τ : Type v} {τ' : Type w}

def evalPtFun (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) : SeriesPoint Φ τ where
  val := fun j => subst (fun n => (w : WittVector p (MvPowerSeries τ R)).coeff n) (f.toPowerSeries j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_eq_zero (WittLaw.hasSubst_coeff w) (WittLaw.constantCoeff_coeff w)
      (f.constantCoeff_eq_zero j)

def evalPt [Φ.IsComm] : CartierModule p Φ →+ WittLaw.seriesPoint p R τ →+ SeriesPoint Φ τ where
  toFun f :=
    { toFun := evalPtFun f
      map_zero' := SeriesPoint.ext (funext fun j => by
        show subst (fun n => ((0 : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n)
          (f.toPowerSeries j) = 0
        simp only [AddSubgroup.coe_zero, WittVector.zero_coeff]
        exact subst_zero_of_constantCoeff_eq_zero (f.constantCoeff_eq_zero j))
      map_add' := evalPtFun_add f }
  map_zero' := AddMonoidHom.ext fun w => SeriesPoint.ext (funext fun j => by
    show subst _ (0 : MvPowerSeries ℕ R) = 0
    rw [← coe_substAlgHom (WittLaw.hasSubst_coeff w), map_zero])
  map_add' f g := AddMonoidHom.ext fun w => SeriesPoint.ext (funext fun j =>
    subst_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero (WittLaw.hasSubst_coeff w) j)

def presPi [Φ.IsComm] {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ)
    (w : ι → WittLaw.seriesPoint p R τ) : SeriesPoint Φ τ :=
  ∑ l, evalPt (f l) (w l)

def presPiHom [Φ.IsComm] {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ) :
    (ι → WittLaw.seriesPoint p R τ) →+ SeriesPoint Φ τ where
  toFun := presPi f
  map_zero' := presPi_zero f
  map_add' := presPi_add f


end CartierModule

end MvFormalGroup

end
