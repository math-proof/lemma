import Mathlib
import Lemma.MvFormalGroup.NegV2
import Structure.CerednikDrinfeld_SpecialFormalModule
import Abbrev.CerednikDrinfeld_SpecialFormalModule

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)

variable (p : ℕ) [Fact p.Prime]

namespace SpecialFormal

variable {p}
variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']


def Series.id (B : Type u) [CommRing B] : Series B := fun i => MvPowerSeries.X i

def Series.comp (ψ φ : Series B) : Series B := fun i => subst φ (ψ i)


def Series.map (f : B →+* B') (φ : Series B) : Series B' := fun i => MvPowerSeries.map f (φ i)


namespace IsLawHom

variable {F G H : MvFormalGroup 2 B} {φ ψ : Series B}

def toHom (h : IsLawHom F G φ) : MvFormalGroup.Hom F G := ⟨φ, h.1, h.2⟩

@[simp] theorem toHom_toPowerSeries (h : IsLawHom F G φ) : h.toHom.toPowerSeries = φ := rfl

theorem of_hom (f : MvFormalGroup.Hom F G) : IsLawHom F G f.toPowerSeries :=
  ⟨f.constantCoeff_eq_zero, f.subst_eq⟩

theorem hasSubst (h : IsLawHom F G φ) : HasSubst φ := hasSubst_of_constantCoeff_zero h.1

theorem id (F : MvFormalGroup 2 B) : IsLawHom F F (Series.id B) := of_hom (MvFormalGroup.Hom.id F)

theorem comp (hψ : IsLawHom G H ψ) (hφ : IsLawHom F G φ) : IsLawHom F H (ψ.comp φ) :=
  of_hom (hψ.toHom.comp hφ.toHom)

theorem map (h : IsLawHom F G φ) (f : B →+* B') :
    IsLawHom (F.map f) (G.map f) (φ.map f) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · show constantCoeff (MvPowerSeries.map f (φ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, h.1 i, map_zero]
  · have hXl : ∀ l : Fin 2, constantCoeff
        ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) = 0 :=
      fun l => constantCoeff_X _
    have hXr : ∀ l : Fin 2, constantCoeff
        ((MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) = 0 :=
      fun l => constantCoeff_X _
    have hA : HasSubst (Sum.elim
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
        fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXl) hXl (h.1 j)
      · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXr) hXr (h.1 j)
    have key := congrArg (MvPowerSeries.map f) (h.2 i)
    rw [map_subst F.hasSubst_toPowerSeries, map_subst hA] at key
    have hAmap : (fun s => MvPowerSeries.map f (Sum.elim
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j)) s))
        = Sum.elim
          (fun j => subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))
              (MvPowerSeries.map f (φ j)))
          (fun j => subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))
              (MvPowerSeries.map f (φ j))) := by
      funext s
      rcases s with j | j
      · show MvPowerSeries.map f (subst _ (φ j)) = _
        rw [map_subst (hasSubst_of_constantCoeff_zero hXl)]
        simp only [MvPowerSeries.map_X, Sum.elim_inl]
      · show MvPowerSeries.map f (subst _ (φ j)) = _
        rw [map_subst (hasSubst_of_constantCoeff_zero hXr)]
        simp only [MvPowerSeries.map_X, Sum.elim_inr]
    rw [hAmap] at key
    exact key

end IsLawHom

theorem Series.map_comp (f : B →+* B') (ψ φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    (ψ.comp φ).map f = (ψ.map f).comp (φ.map f) := by
  funext i
  show MvPowerSeries.map f (subst φ (ψ i)) = subst _ (MvPowerSeries.map f (ψ i))
  rw [map_subst (hasSubst_of_constantCoeff_zero hφ)]
  rfl

theorem Series.map_addVia (f : B →+* B') (F : MvFormalGroup 2 B) (φ ψ : Series B)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    (Series.addVia F φ ψ).map f = Series.addVia (F.map f) (φ.map f) (ψ.map f) := by
  funext i
  show MvPowerSeries.map f (subst (Sum.elim φ ψ) (F.toPowerSeries i)) =
    subst (Sum.elim (φ.map f) (ψ.map f)) (MvPowerSeries.map f (F.toPowerSeries i))
  have hS : HasSubst (Sum.elim φ ψ) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact hφ j
    · exact hψ j
  rw [map_subst hS]
  congr 1
  funext s
  rcases s with j | j <;> rfl

@[simp] theorem Series.map_id (f : B →+* B') : (Series.id B).map f = Series.id B' := by
  funext i
  exact MvPowerSeries.map_X f i

@[simp] theorem Series.map_ringHom_id (φ : Series B) : φ.map (RingHom.id B) = φ := by
  funext i
  exact congrFun (congrArg DFunLike.coe (MvPowerSeries.map_id (σ := Fin 2) (R := B))) (φ i)

theorem Series.map_map {B'' : Type*} [CommRing B''] (f : B →+* B') (g : B' →+* B'') (φ : Series B) :
    (φ.map f).map g = φ.map (g.comp f) := by
  funext i
  exact MvPowerSeries.map_map f g (φ i)


theorem Series.comp_id (φ : Series B) : φ.comp (Series.id B) = φ := by
  funext i
  exact congrFun MvPowerSeries.subst_self (φ i)

theorem Series.constantCoeff_comp {ψ φ : Series B} (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin 2) : constantCoeff ((ψ.comp φ) i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hφ) hφ (hψ i)

end SpecialFormal

open SpecialFormal


namespace FormalODModule


variable {p}
variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']

def map (f : B →+* B') (X : FormalODModule p B) : FormalODModule p B' where
  F := X.F.map f
  isComm := by
    constructor
    intro i
    have key := congrArg (MvPowerSeries.map f) (X.isComm.comm i)
    have hS : HasSubst (Sum.elim
        (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
        fun j => MvPowerSeries.X (Sum.inl j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j) <;> exact constantCoeff_X _
    rw [map_subst hS] at key
    have hfam : (fun s => MvPowerSeries.map f (Sum.elim
        (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
        (fun j => MvPowerSeries.X (Sum.inl j)) s))
        = Sum.elim
          (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))
          fun j => MvPowerSeries.X (Sum.inl j) := by
      funext s
      rcases s with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, MvPowerSeries.map_X]
    rw [hfam] at key
    exact key
  act a := (X.act a).map f
  varpi := X.varpi.map f
  isLawHom_act a := (X.isLawHom_act a).map f
  isLawHom_varpi := X.isLawHom_varpi.map f
  act_one := by rw [X.act_one, Series.map_id]
  act_mul a b := by
    rw [X.act_mul, Series.map_comp f _ _ (X.isLawHom_act b).1]
  act_add a b := by
    rw [X.act_add, Series.map_addVia f X.F _ _ (X.isLawHom_act a).1 (X.isLawHom_act b).1]
  varpi_comp_varpi := by
    rw [← Series.map_comp f _ _ X.isLawHom_varpi.1, X.varpi_comp_varpi]
  varpi_comp_act a := by
    rw [← Series.map_comp f _ _ (X.isLawHom_act a).1, X.varpi_comp_act,
      Series.map_comp f _ _ X.isLawHom_varpi.1]

@[simp] theorem map_F (f : B →+* B') (X : FormalODModule p B) : (X.map f).F = X.F.map f := rfl
@[simp] theorem map_act (f : B →+* B') (X : FormalODModule p B) (a : Zp2 p) :
    (X.map f).act a = (X.act a).map f := rfl
@[simp] theorem map_varpi (f : B →+* B') (X : FormalODModule p B) :
    (X.map f).varpi = X.varpi.map f := rfl

theorem ext' {X Y : FormalODModule p B} (hF : X.F = Y.F) (ha : X.act = Y.act)
    (hv : X.varpi = Y.varpi) : X = Y := by
  cases X; cases Y; cases hF; cases ha; cases hv; rfl

theorem _root_.MvFormalGroup.map_map' {g : ℕ} {B'' : Type*} [CommRing B''] (f : B →+* B')
    (f' : B' →+* B'') (F : MvFormalGroup g B) : (F.map f).map f' = F.map (f'.comp f) :=
  MvFormalGroup.ext (funext fun i => MvPowerSeries.map_map f f' (F.toPowerSeries i))

theorem _root_.MvFormalGroup.map_ringHom_id {g : ℕ} (F : MvFormalGroup g B) : F.map (RingHom.id B) = F :=
  MvFormalGroup.ext (funext fun i => by
    show MvPowerSeries.map (RingHom.id B) (F.toPowerSeries i) = F.toPowerSeries i
    rw [MvPowerSeries.map_id]; rfl)

@[simp] theorem map_id (X : FormalODModule p B) : X.map (RingHom.id B) = X :=
  ext' (MvFormalGroup.map_ringHom_id X.F) (funext fun a => Series.map_ringHom_id (X.act a))
    (Series.map_ringHom_id _)

theorem map_map {B'' : Type*} [CommRing B''] (f : B →+* B') (g : B' →+* B'')
    (X : FormalODModule p B) : (X.map f).map g = X.map (g.comp f) :=
  ext' (MvFormalGroup.map_map' f g X.F) (funext fun a => Series.map_map f g (X.act a))
    (Series.map_map f g _)

def actEnd (X : FormalODModule p B) (a : Zp2 p) : MvFormalGroup.End X.F := (X.isLawHom_act a).toHom

def varpiEnd (X : FormalODModule p B) : MvFormalGroup.End X.F := X.isLawHom_varpi.toHom

def actRingHom (X : FormalODModule p B) : Zp2 p →+* MvFormalGroup.End X.F where
  toFun := X.actEnd
  map_one' := MvFormalGroup.Hom.ext (X.act_one)
  map_mul' a b := MvFormalGroup.Hom.ext (X.act_mul a b)
  map_zero' := by
    have h : X.actEnd 0 + X.actEnd 0 = X.actEnd 0 :=
      MvFormalGroup.Hom.ext (by have h := (X.act_add 0 0).symm; rw [add_zero] at h; exact h)
    exact add_eq_left.mp h
  map_add' a b := MvFormalGroup.Hom.ext (X.act_add a b)

@[simp] theorem actRingHom_apply (X : FormalODModule p B) (a : Zp2 p) :
    X.actRingHom a = X.actEnd a := rfl

@[simp] theorem actEnd_toPowerSeries (X : FormalODModule p B) (a : Zp2 p) :
    (X.actEnd a).toPowerSeries = X.act a := rfl

@[simp] theorem varpiEnd_toPowerSeries (X : FormalODModule p B) :
    X.varpiEnd.toPowerSeries = X.varpi := rfl

theorem varpiEnd_mul_varpiEnd (X : FormalODModule p B) :
    X.varpiEnd * X.varpiEnd = X.actRingHom (p : Zp2 p) :=
  MvFormalGroup.Hom.ext X.varpi_comp_varpi

theorem varpiEnd_mul_actEnd (X : FormalODModule p B) (a : Zp2 p) :
    X.varpiEnd * X.actEnd a = X.actEnd (WittVector.frobenius a) * X.varpiEnd :=
  MvFormalGroup.Hom.ext (X.varpi_comp_act a)

theorem act_natCast (X : FormalODModule p B) (n : ℕ) : X.act (n : Zp2 p) = X.F.nthSeries n := by
  have h : X.actRingHom (n : Zp2 p) = (n : MvFormalGroup.End X.F) := map_natCast X.actRingHom n
  have h2 := congrArg MvFormalGroup.Hom.toPowerSeries h
  rw [MvFormalGroup.End.toPowerSeries_natCast] at h2
  exact h2

theorem act_pow_add (X : FormalODModule p B) (a b : ℕ) :
    X.act ((p : Zp2 p) ^ (a + b)) = (X.act ((p : Zp2 p) ^ a)).comp (X.act ((p : Zp2 p) ^ b)) := by
  rw [pow_add, X.act_mul]


namespace IsODHom

variable {X Y Z : FormalODModule p B} {φ ψ : Series B}


protected theorem id (X : FormalODModule p B) : IsODHom X X (Series.id B) := by
  refine ⟨IsLawHom.id X.F, fun a => ?_, ?_⟩
  · rw [Series.id_comp _ (X.isLawHom_act a).1, Series.comp_id]
  · rw [Series.id_comp _ X.isLawHom_varpi.1, Series.comp_id]

protected theorem comp (hψ : IsODHom Y Z ψ) (hφ : IsODHom X Y φ) : IsODHom X Z (ψ.comp φ) := by
  refine ⟨hψ.1.comp hφ.1, fun a => ?_, ?_⟩
  · rw [Series.comp_assoc _ _ _ hφ.constantCoeff (X.isLawHom_act a).1, hφ.2.1 a,
      ← Series.comp_assoc _ _ _ (Y.isLawHom_act a).1 hφ.constantCoeff, hψ.2.1 a,
      Series.comp_assoc _ _ _ hψ.constantCoeff hφ.constantCoeff]
  · rw [Series.comp_assoc _ _ _ hφ.constantCoeff X.isLawHom_varpi.1, hφ.2.2,
      ← Series.comp_assoc _ _ _ Y.isLawHom_varpi.1 hφ.constantCoeff, hψ.2.2,
      Series.comp_assoc _ _ _ hψ.constantCoeff hφ.constantCoeff]

protected theorem map (h : IsODHom X Y φ) (f : B →+* B') :
    IsODHom (X.map f) (Y.map f) (φ.map f) := by
  refine ⟨h.1.map f, fun a => ?_, ?_⟩
  · show (φ.map f).comp ((X.act a).map f) = ((Y.act a).map f).comp (φ.map f)
    rw [← Series.map_comp f _ _ (X.isLawHom_act a).1, h.2.1 a, Series.map_comp f _ _ h.constantCoeff]
  · show (φ.map f).comp (X.varpi.map f) = (Y.varpi.map f).comp (φ.map f)
    rw [← Series.map_comp f _ _ X.isLawHom_varpi.1, h.2.2, Series.map_comp f _ _ h.constantCoeff]

theorem act_natCast_pow (X : FormalODModule p B) (n : ℕ) :
    IsODHom X X (X.act ((p : Zp2 p) ^ n)) := by
  refine ⟨X.isLawHom_act _, fun a => ?_, ?_⟩
  · rw [← X.act_mul, ← X.act_mul, mul_comm]
  · rw [X.varpi_comp_act, map_pow, map_natCast]

end IsODHom

namespace Hom

variable {X Y Z : FormalODModule p B}

@[ext] theorem ext {f g : Hom X Y} (h : f.toSeries = g.toSeries) : f = g := by
  cases f; cases g; cases h; rfl

protected def id (X : FormalODModule p B) : Hom X X := ⟨Series.id B, IsODHom.id X⟩

def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z := ⟨g.toSeries.comp f.toSeries, g.isODHom.comp f.isODHom⟩

def map (f' : B →+* B') (f : Hom X Y) : Hom (X.map f') (Y.map f') :=
  ⟨f.toSeries.map f', f.isODHom.map f'⟩

def toLawHom (f : Hom X Y) : MvFormalGroup.Hom X.F Y.F := f.isODHom.1.toHom

def IsIso (f : Hom X Y) : Prop := ∃ g : Hom Y X, g.comp f = Hom.id X ∧ f.comp g = Hom.id Y

end Hom


def IsIsogenyOfHeight (X Y : FormalODModule p B) (φ : Series B) (h : ℕ) : Prop :=
  IsODHom X Y φ ∧ HasKernelOfDegree φ (p ^ h)


end FormalODModule


namespace SpecialFormal


variable {p}

def residueMap {O : Type v} [CommRing O] {B : Type u} [CommRing B] (ψ : O →+* B) :
    O ⧸ pIdeal p O →+* B ⧸ pIdeal p B :=
  Ideal.quotientMap (pIdeal p B) ψ (by
    rw [pIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
      map_natCast]
    exact Ideal.subset_span rfl)

def reduceMap {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B') :
    B ⧸ pIdeal p B →+* B' ⧸ pIdeal p B' :=
  residueMap f

abbrev structureMap {O : Type v} [CommRing O] {B : Type u} [CommRing B] (ι : Zp2 p →+* O)
    (ψ : O →+* B) : Zp2 p →+* B :=
  ψ.comp ι


namespace Rigidified

variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B B' B'' : Type u} [CommRing B] [CommRing B'] [CommRing B'']

abbrev Xbar (t : Rigidified p Φ B) : FormalODModule p (B ⧸ pIdeal p B) :=
  t.X.map (Ideal.Quotient.mk (pIdeal p B))

abbrev Φbar (ψ : O →+* B) (_t : Rigidified p Φ B) : FormalODModule p (B ⧸ pIdeal p B) :=
  Φ.map (residueMap ψ)

def IsAdmissible (ι : Zp2 p →+* O) (ψ : O →+* B) (t : Rigidified p Φ B) : Prop :=
  t.X.IsSpecial (structureMap ι ψ) ∧ t.X.HasHeight 4 ∧
    FormalODModule.IsIsogenyOfHeight (t.Φbar ψ) t.Xbar t.ρ (4 * t.n)

def IsIsomorphic (t t' : Rigidified p Φ B) : Prop :=
  ∃ (u v : Series B) (m : ℕ), FormalODModule.IsODHom t.X t'.X u ∧ FormalODModule.IsODHom t'.X t.X v ∧
    v.comp u = Series.id B ∧ u.comp v = Series.id B ∧
    (t'.Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp ((u.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ)
      = (t'.Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp t'.ρ

theorem IsIsomorphic.refl (t : Rigidified p Φ B) (hρ : ∀ i, constantCoeff (t.ρ i) = 0) :
    t.IsIsomorphic t := by
  refine ⟨Series.id B, Series.id B, 0, FormalODModule.IsODHom.id t.X, FormalODModule.IsODHom.id t.X,
    Series.comp_id _, Series.comp_id _, ?_⟩
  rw [Series.map_id, Series.id_comp _ hρ]

theorem IsAdmissible.constantCoeff_ρ {ι : Zp2 p →+* O} {ψ : O →+* B} {t : Rigidified p Φ B}
    (ht : t.IsAdmissible ι ψ) (i : Fin 2) : constantCoeff (t.ρ i) = 0 :=
  ht.2.2.1.constantCoeff i

theorem IsIsomorphic.symm {t t' : Rigidified p Φ B} (h : t.IsIsomorphic t')
    (hρ : ∀ i, constantCoeff (t.ρ i) = 0) (hρ' : ∀ i, constantCoeff (t'.ρ i) = 0) :
    t'.IsIsomorphic t := by
  obtain ⟨u, v, m, hu, hv, hvu, huv, h⟩ := h
  refine ⟨v, u, m, hv, hu, huv, hvu, ?_⟩
  set mk := Ideal.Quotient.mk (pIdeal p B)
  have hub : FormalODModule.IsODHom t.Xbar t'.Xbar (u.map mk) := hu.map mk
  have hvb : FormalODModule.IsODHom t'.Xbar t.Xbar (v.map mk) := hv.map mk
  have hA' : ∀ k i, constantCoeff (t'.Xbar.act ((p : Zp2 p) ^ k) i) = 0 :=
    fun k => (t'.Xbar.isLawHom_act _).1
  have huρ : ∀ i, constantCoeff (((u.map mk).comp t.ρ) i) = 0 :=
    Series.constantCoeff_comp hub.constantCoeff hρ
  have hvu' : (v.map mk).comp (u.map mk) = Series.id _ := by
    rw [← Series.map_comp mk _ _ hu.constantCoeff, hvu, Series.map_id]
  rw [← Series.comp_assoc _ _ _ hvb.constantCoeff hρ', ← hvb.2.1, Series.comp_assoc _ _ _ (hA' _) hρ',
    ← h, ← Series.comp_assoc _ _ _ (hA' _) huρ, hvb.2.1, Series.comp_assoc _ _ _ hvb.constantCoeff huρ,
    ← Series.comp_assoc _ _ _ hub.constantCoeff hρ, hvu', Series.id_comp _ hρ]

theorem IsIsomorphic.trans {t t' t'' : Rigidified p Φ B} (h₁ : t.IsIsomorphic t') (h₂ : t'.IsIsomorphic t'')
    (hρ : ∀ i, constantCoeff (t.ρ i) = 0) (hρ' : ∀ i, constantCoeff (t'.ρ i) = 0)
    (hρ'' : ∀ i, constantCoeff (t''.ρ i) = 0) :
    t.IsIsomorphic t'' := by
  obtain ⟨u₁, v₁, m₁, hu₁, hv₁, hvu₁, huv₁, h₁⟩ := h₁
  obtain ⟨u₂, v₂, m₂, hu₂, hv₂, hvu₂, huv₂, h₂⟩ := h₂
  refine ⟨u₂.comp u₁, v₁.comp v₂, m₁ + m₂ + t'.n, hu₂.comp hu₁, hv₁.comp hv₂, ?_, ?_, ?_⟩
  · rw [Series.comp_assoc _ _ _ hv₂.constantCoeff (hu₂.comp hu₁).constantCoeff,
      ← Series.comp_assoc _ _ _ hu₂.constantCoeff hu₁.constantCoeff, hvu₂,
      Series.id_comp _ hu₁.constantCoeff, hvu₁]
  · rw [Series.comp_assoc _ _ _ hu₁.constantCoeff (hv₁.comp hv₂).constantCoeff,
      ← Series.comp_assoc _ _ _ hv₁.constantCoeff hv₂.constantCoeff, huv₁,
      Series.id_comp _ hv₂.constantCoeff, huv₂]
  set mk := Ideal.Quotient.mk (pIdeal p B)
  have hub₁ : FormalODModule.IsODHom t.Xbar t'.Xbar (u₁.map mk) := hu₁.map mk
  have hub₂ : FormalODModule.IsODHom t'.Xbar t''.Xbar (u₂.map mk) := hu₂.map mk
  have hA' : ∀ k i, constantCoeff (t'.Xbar.act ((p : Zp2 p) ^ k) i) = 0 :=
    fun k => (t'.Xbar.isLawHom_act _).1
  have hA'' : ∀ k i, constantCoeff (t''.Xbar.act ((p : Zp2 p) ^ k) i) = 0 :=
    fun k => (t''.Xbar.isLawHom_act _).1
  have hu₁ρ : ∀ i, constantCoeff (((u₁.map mk).comp t.ρ) i) = 0 :=
    Series.constantCoeff_comp hub₁.constantCoeff hρ
  have hu₂ρ' : ∀ i, constantCoeff (((u₂.map mk).comp t'.ρ) i) = 0 :=
    Series.constantCoeff_comp hub₂.constantCoeff hρ'
  have e₁ : m₁ + m₂ + t'.n + t''.n = (m₂ + t''.n) + (m₁ + t'.n) := by omega
  have e₂ : m₁ + m₂ + t'.n + t.n = (m₁ + t.n) + (m₂ + t'.n) := by omega
  rw [Series.map_comp mk _ _ hu₁.constantCoeff, e₁, e₂, FormalODModule.act_pow_add t''.Xbar (m₂ + t''.n) (m₁ + t'.n),
    Series.comp_assoc _ _ _ hub₁.constantCoeff hρ,
    Series.comp_assoc _ _ _ (hA'' _) (Series.constantCoeff_comp hub₂.constantCoeff hu₁ρ),
    ← Series.comp_assoc _ _ _ hub₂.constantCoeff hu₁ρ, ← hub₂.2.1,
    Series.comp_assoc _ _ _ (hA' _) hu₁ρ, h₁,
    ← Series.comp_assoc _ _ _ (hA' _) hρ', hub₂.2.1,
    Series.comp_assoc _ _ _ hub₂.constantCoeff hρ',
    ← Series.comp_assoc _ _ _ (hA'' _) hu₂ρ', ← FormalODModule.act_pow_add t''.Xbar (m₂ + t''.n) (m₁ + t.n),
    add_comm (m₂ + t''.n) (m₁ + t.n), FormalODModule.act_pow_add t''.Xbar (m₁ + t.n) (m₂ + t''.n),
    Series.comp_assoc _ _ _ (hA'' _) hu₂ρ', h₂,
    ← Series.comp_assoc _ _ _ (hA'' _) hρ'', ← FormalODModule.act_pow_add]

def map (f : B →+* B') (t : Rigidified p Φ B) : Rigidified p Φ B' where
  X := t.X.map f
  n := t.n
  ρ := t.ρ.map (reduceMap f)

@[simp] theorem map_X (f : B →+* B') (t : Rigidified p Φ B) : (t.map f).X = t.X.map f := rfl
@[simp] theorem map_n (f : B →+* B') (t : Rigidified p Φ B) : (t.map f).n = t.n := rfl
@[simp] theorem map_ρ (f : B →+* B') (t : Rigidified p Φ B) :
    (t.map f).ρ = t.ρ.map (reduceMap f) := rfl

theorem ext' {t t' : Rigidified p Φ B} (hX : t.X = t'.X) (hn : t.n = t'.n) (hρ : t.ρ = t'.ρ) :
    t = t' := by
  cases t; cases t'; cases hX; cases hn; cases hρ; rfl

omit [Fact p.Prime] in
theorem reduceMap_id : reduceMap (p := p) (RingHom.id B) = RingHom.id _ :=
  Ideal.Quotient.ringHom_ext rfl

omit [Fact p.Prime] in
theorem reduceMap_comp (g : B' →+* B'') (f : B →+* B') :
    reduceMap (p := p) (g.comp f) = (reduceMap g).comp (reduceMap f) :=
  Ideal.Quotient.ringHom_ext rfl

omit [Fact p.Prime] in

theorem _root_.CerednikDrinfeld.SpecialFormal.residueMap_comp (f : B →+* B') (ψ : O →+* B) :
    residueMap (p := p) (f.comp ψ) = (reduceMap f).comp (residueMap ψ) :=
  Ideal.Quotient.ringHom_ext rfl

theorem map_id (t : Rigidified p Φ B) : t.map (RingHom.id B) = t :=
  ext' (by rw [map_X]; exact t.X.map_id) rfl (by rw [map_ρ, reduceMap_id, Series.map_ringHom_id])

theorem map_comp (g : B' →+* B'') (f : B →+* B') (t : Rigidified p Φ B) :
    t.map (g.comp f) = (t.map f).map g :=
  ext' (by rw [map_X, map_X, map_X, FormalODModule.map_map]) rfl
    (by rw [map_ρ, map_ρ, map_ρ, reduceMap_comp, Series.map_map])

theorem Φbar_map (ψ : O →+* B) (f : B →+* B') (t : Rigidified p Φ B) :
    (t.map f).Φbar (f.comp ψ) = (t.Φbar ψ).map (reduceMap f) := by
  rw [Φbar, Φbar, FormalODModule.map_map, residueMap_comp]

end Rigidified


namespace ModuliPackage

variable {O : Type v} [CommRing O]

def twist (τ : O →+* O) (M : ModuliPackage.{u, v} p O) : ModuliPackage.{u, v} p O where
  obj B _ ψ hB := M.obj B (ψ.comp τ) hB
  map hB hB' f hf := M.map hB hB' f (by rw [← RingHom.comp_assoc, hf])
  map_id hB x := M.map_id hB x
  map_comp hB hB' hB'' g f hf hg x := M.map_comp hB hB' hB'' g f _ _ x

@[simp] theorem twist_obj (τ : O →+* O) (M : ModuliPackage.{u, v} p O) (B : Type u) [CommRing B]
    (ψ : O →+* B) (hB : IsNilpotent (p : B)) : (M.twist τ).obj B ψ hB = M.obj B (ψ.comp τ) hB := rfl

theorem twist_map (τ : O →+* O) (M : ModuliPackage.{u, v} p O) {B B' : Type u} [CommRing B]
    [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'} (hB : IsNilpotent (p : B))
    (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ') (x : (M.twist τ).obj B ψ hB) :
    (M.twist τ).map hB hB' f hf x =
      M.map (ψ := ψ.comp τ) (ψ' := ψ'.comp τ) hB hB' f (by rw [← RingHom.comp_assoc, hf]) x := rfl

def IsZariskiSheaf (M : ModuliPackage.{u, v} p O) : Prop :=
  ∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (n : ℕ) (f : Fin n → B) (_hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type u) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)]
    [∀ i, IsLocalization.Away (f i) (L i)]
    (hL : ∀ i, IsNilpotent (p : L i))
    (L₂ : Fin n → Fin n → Type u) [∀ i j, CommRing (L₂ i j)] [∀ i j, Algebra B (L₂ i j)]
    [∀ i j, IsLocalization.Away (f i * f j) (L₂ i j)]
    (hL₂ : ∀ i j, IsNilpotent (p : L₂ i j))
    (l : ∀ i j, L i →+* L₂ i j) (r : ∀ i j, L j →+* L₂ i j)
    (hl : ∀ i j (b : B), l i j (algebraMap B (L i) b) = algebraMap B (L₂ i j) b)
    (hr : ∀ i j (b : B), r i j (algebraMap B (L j) b) = algebraMap B (L₂ i j) b),
    (∀ m m' : M.obj B ψ hB,
      (∀ i, M.map (ψ' := (algebraMap B (L i)).comp ψ) hB (hL i) (algebraMap B (L i)) rfl m =
        M.map (ψ' := (algebraMap B (L i)).comp ψ) hB (hL i) (algebraMap B (L i)) rfl m') →
      m = m') ∧
    (∀ x : ∀ i, M.obj (L i) ((algebraMap B (L i)).comp ψ) (hL i),
      (∀ i j, M.map (ψ' := (algebraMap B (L₂ i j)).comp ψ) (hL i) (hL₂ i j) (l i j)
            (RingHom.ext fun b => hl i j (ψ b)) (x i) =
          M.map (ψ' := (algebraMap B (L₂ i j)).comp ψ) (hL j) (hL₂ i j) (r i j)
            (RingHom.ext fun b => hr i j (ψ b)) (x j)) →
      ∃ m : M.obj B ψ hB, ∀ i,
        M.map (ψ' := (algebraMap B (L i)).comp ψ) hB (hL i) (algebraMap B (L i)) rfl m = x i)

def IsModuli (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (M : ModuliPackage.{u, v} p O) : Prop :=
  M.IsZariskiSheaf ∧
  ∃ η : ∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      Rigidified p Φ B → M.obj B ψ hB,
    (∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
        (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
        (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
    (∀ (B B' : Type u) [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B')
        (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
        (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
        η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
    (∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
        ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
          ∀ (i : Fin n) (L : Type u) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L]
            (hL : IsNilpotent (p : L)),
            ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
              η L ((algebraMap B L).comp ψ) hL t =
                M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)

end ModuliPackage

end SpecialFormal

end CerednikDrinfeld

end
