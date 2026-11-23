import Mathlib
import Def.FormalGroup_NegV2
import Structure.CerednikDrinfeld_SpecialFormalModule
import Def.MvFormalGroup_BasicV2
import Instance.MvFormalGroup_EndRingV2
import Instance.MvFormalGroup_NegV2
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

namespace IsLawHom

variable {F G H : MvFormalGroup 2 B} {φ ψ : Series B}

def toHom (h : IsLawHom F G φ) : MvFormalGroup.Hom F G := ⟨φ, h.1, h.2⟩

end IsLawHom

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


namespace Hom

variable {X Y Z : FormalODModule p B}

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

def map (f : B →+* B') (t : Rigidified p Φ B) : Rigidified p Φ B' where
  X := t.X.map f
  n := t.n
  ρ := t.ρ.map (reduceMap f)

end Rigidified


namespace ModuliPackage

variable {O : Type v} [CommRing O]

def twist (τ : O →+* O) (M : ModuliPackage.{u, v} p O) : ModuliPackage.{u, v} p O where
  obj B _ ψ hB := M.obj B (ψ.comp τ) hB
  map hB hB' f hf := M.map hB hB' f (by rw [← RingHom.comp_assoc, hf])
  map_id hB x := M.map_id hB x
  map_comp hB hB' hB'' g f hf hg x := M.map_comp hB hB' hB'' g f _ _ x

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
