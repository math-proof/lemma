module

public import Mathlib
public import Def.FormalGroup_NegV2
public import Def.FormalGroup_Weight
public import Def.FormalGroup_CartierModuleInBlk
public import Structure.MvFormalGroup_CartierModule
public import Def.MvFormalGroup_BasicV2
public import Instance.MvFormalGroup_EndRingV2
public import Theorem.MvPowerSeries.CartierModuleSubst
public import Theorem.MvPowerSeries.CartierModuleInBlk

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]


namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

omit hp in
protected def zero (Φ : MvFormalGroup d R) : CartierModule p Φ where
  toPowerSeries := fun _ => 0
  constantCoeff_eq_zero := fun _ => map_zero _
  subst_eq := by
    intro j
    rw [← coe_substAlgHom (hasSubst_addFam p R), map_zero]
    have h0 : (fun l : Fin d => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R))
        ((fun _ : Fin d => (0 : MvPowerSeries ℕ R)) l)) = fun _ => 0 := inBlk_zero 0
    have h1 : (fun l : Fin d => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R))
        ((fun _ : Fin d => (0 : MvPowerSeries ℕ R)) l)) = fun _ => 0 := inBlk_zero 1
    rw [h0, h1]
    exact (subst_elim_zero_right Φ (fun _ => map_zero _) j).symm

protected def add [Φ.IsComm] (f g : CartierModule p Φ) : CartierModule p Φ where
  toPowerSeries := fun j => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero j
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hg := g.constantCoeff_eq_zero
    show subst (WittLaw.addFam p R)
        (subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j)) =
      subst (Sum.elim
        (inBlk 0 fun l => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries l))
        (inBlk 1 fun l => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries l)))
        (Φ.toPowerSeries j)
    rw [subst_subst_elim Φ hf hg (hasSubst_addFam p R) j, inBlk_subst_elim Φ 0 hf hg,
      inBlk_subst_elim Φ 1 hf hg]
    have hfeq : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    have hgeq : (fun l => subst (WittLaw.addFam p R) (g.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 g.toPowerSeries) (inBlk 1 g.toPowerSeries))
          (Φ.toPowerSeries l) := funext g.subst_addFam
    rw [hfeq, hgeq]
    exact subst_elim_exchange Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf)
      (constantCoeff_inBlk 0 hg) (constantCoeff_inBlk 1 hg) j

protected def neg [Φ.IsComm] (f : CartierModule p Φ) : CartierModule p Φ where
  toPowerSeries := negSeries Φ f.toPowerSeries
  constantCoeff_eq_zero := constantCoeff_negSeries Φ f.toPowerSeries
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hneg : ∀ j, (negSeries Φ f.toPowerSeries j).constantCoeff = 0 :=
      constantCoeff_negSeries Φ _
    show subst (WittLaw.addFam p R) (negSeries Φ f.toPowerSeries j) =
      subst (Sum.elim (inBlk 0 (negSeries Φ f.toPowerSeries)) (inBlk 1 (negSeries Φ f.toPowerSeries)))
        (Φ.toPowerSeries j)

    have hS : (fun l => subst (WittLaw.addFam p R) (negSeries Φ f.toPowerSeries l)) =
        negSeries Φ fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l) := by
      have hA := hasSubst_addFam p R
      have hA0 := constantCoeff_addFam p R
      refine negSeries_unique Φ (fun l => constantCoeff_subst_eq_zero hA hA0 (hf l))
        (fun l => constantCoeff_subst_eq_zero hA hA0 (hneg l)) fun i => ?_
      rw [← subst_subst_elim Φ hf hneg hA i, subst_elim_negSeries Φ hf i, ← coe_substAlgHom hA,
        map_zero]
    have h1 := congrFun hS j
    rw [h1]
    have hfeq : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    rw [hfeq, negSeries_elim_add Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf),
      ← inBlk_negSeries Φ 0 hf, ← inBlk_negSeries Φ 1 hf]

end CartierModule

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

def precompFun {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    CartierModule p Φ where
  toPowerSeries := fun j => subst u (f.toPowerSeries j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_eq_zero hu.hasSubst hu.constantCoeff (f.constantCoeff_eq_zero j)
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hA := hasSubst_addFam p R
    have hP := hasSubst_pairFam hu.hasSubst hu.constantCoeff
    show subst (WittLaw.addFam p R) (subst u (f.toPowerSeries j)) =
      subst (Sum.elim (inBlk 0 fun l => subst u (f.toPowerSeries l))
        (inBlk 1 fun l => subst u (f.toPowerSeries l))) (Φ.toPowerSeries j)
    rw [subst_comp_subst_apply hu.hasSubst hA]
    have hfam : (fun n => subst (WittLaw.addFam p R) (u n)) =
        fun n => subst (WittLaw.pairFam u) (WittLaw.addFam p R n) := funext hu.subst_addFam
    rw [hfam, ← subst_comp_subst_apply hA hP, f.subst_addFam, subst_subst_elim Φ
      (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) hP]
    congr 1
    funext s
    rcases s with l | l
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 0 (f.toPowerSeries l)
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 1 (f.toPowerSeries l)

def precomp [Φ.IsComm] {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u) :
    CartierModule p Φ →+ CartierModule p Φ where
  toFun := precompFun hu
  map_zero' := CartierModule.ext (funext fun j => by
    show subst u (0 : MvPowerSeries ℕ R) = 0
    rw [← coe_substAlgHom hu.hasSubst, map_zero])
  map_add' f g := CartierModule.ext (funext fun j =>
    subst_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero hu.hasSubst j)

def frobenius [Φ.IsComm] : CartierModule p Φ →+ CartierModule p Φ :=
  precomp (WittLaw.isEndo_verFam R)

def verschiebung [Φ.IsComm] [CharP R p] : CartierModule p Φ →+ CartierModule p Φ :=
  precomp (WittLaw.isEndo_frobFam R)

def mapFun (φ : Φ.Hom Φ') (f : CartierModule p Φ) : CartierModule p Φ' where
  toPowerSeries := fun i => subst f.toPowerSeries (φ.toPowerSeries i)
  constantCoeff_eq_zero := fun i =>
    constantCoeff_subst_eq_zero f.hasSubst_toPowerSeries f.constantCoeff_eq_zero
      (φ.constantCoeff_eq_zero i)
  subst_eq := by
    intro i
    have hf := f.constantCoeff_eq_zero
    show subst (WittLaw.addFam p R) (subst f.toPowerSeries (φ.toPowerSeries i)) =
      subst (Sum.elim (inBlk 0 fun l => subst f.toPowerSeries (φ.toPowerSeries l))
        (inBlk 1 fun l => subst f.toPowerSeries (φ.toPowerSeries l))) (Φ'.toPowerSeries i)
    rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_addFam p R)]
    have hfam : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    rw [hfam, φ.subst_subst_elim (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) i]
    congr 1
    funext s
    rcases s with l | l
    · show subst (inBlk 0 f.toPowerSeries) (φ.toPowerSeries l) =
        subst (blk 0) (subst f.toPowerSeries (φ.toPowerSeries l))
      rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_blk 0)]
      rfl
    · show subst (inBlk 1 f.toPowerSeries) (φ.toPowerSeries l) =
        subst (blk 1) (subst f.toPowerSeries (φ.toPowerSeries l))
      rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_blk 1)]
      rfl

def map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') : CartierModule p Φ →+ CartierModule p Φ' where
  toFun := mapFun φ
  map_zero' := CartierModule.ext (funext fun i =>
    subst_zero_of_constantCoeff_eq_zero (φ.constantCoeff_eq_zero i))
  map_add' f g := CartierModule.ext (funext fun i =>
    φ.subst_subst_elim f.constantCoeff_eq_zero g.constantCoeff_eq_zero i)

def endAct [Φ.IsComm] : MvFormalGroup.End Φ →+* AddMonoid.End (CartierModule p Φ) where
  toFun φ := map φ
  map_one' := AddMonoidHom.ext map_id
  map_mul' φ ψ := AddMonoidHom.ext (map_comp φ ψ)
  map_zero' := AddMonoidHom.ext map_zero_hom
  map_add' φ ψ := AddMonoidHom.ext (map_add_hom φ ψ)

end CartierModule

namespace WittLaw

def nsmulFam (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (n : ℕ) : ℕ → MvPowerSeries ℕ R :=
  fun k => ((MvPolynomial.map (Int.castRingHom R)
    (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n k)) : MvPolynomial ℕ R) :
      MvPowerSeries ℕ R)

variable (p R) in

def stepFam (n : ℕ) : Fin 2 × ℕ → MvPowerSeries ℕ R :=
  fun im => Fin.cases (nsmulFam p R n im.2) (fun _ => X im.2) im.1

end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

def tangent [Φ.IsComm] : CartierModule p Φ →+ (Fin d → R) where
  toFun f := fun j => coeff (Finsupp.single 0 1) (f.toPowerSeries j)
  map_zero' := by
    funext j
    simp
  map_add' f g := by
    funext j
    show coeff (Finsupp.single 0 1) (subst (Sum.elim f.toPowerSeries g.toPowerSeries)
      (Φ.toPowerSeries j)) = _
    have h0 : ∀ s, ((Sum.elim f.toPowerSeries g.toPowerSeries) s).constantCoeff = 0 := by
      rintro (l | l)
      exacts [f.constantCoeff_eq_zero l, g.constantCoeff_eq_zero l]
    rw [coeff_single_subst h0, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Φ.coeff_single_inl, Φ.coeff_single_inr, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl

def curveFam (R : Type u) [CommRing R] : ℕ → PowerSeries R
  | 0 => PowerSeries.X
  | _ + 1 => 0

omit hp in
def curve (f : CartierModule p Φ) : Fin d → PowerSeries R :=
  fun j => subst (curveFam R) (f.toPowerSeries j)

namespace Examples

def addLinear (p : ℕ) [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R] (v : Fin d → R) :
    CartierModule p (addMv d R) where
  toPowerSeries := fun i => v i • (X 0 : MvPowerSeries ℕ R)
  constantCoeff_eq_zero := fun i => by simp
  subst_eq := by
    intro i
    have hc : ∀ l, ((fun l => v l • (X 0 : MvPowerSeries ℕ R)) l).constantCoeff = 0 :=
      fun l => by simp
    have h0 : ∀ s, ((Sum.elim (inBlk 0 fun l => v l • (X 0 : MvPowerSeries ℕ R))
        (inBlk 1 fun l => v l • (X 0 : MvPowerSeries ℕ R))) s).constantCoeff = 0 := by
      rintro (l | l)
      exacts [constantCoeff_inBlk 0 hc l, constantCoeff_inBlk 1 hc l]
    show subst (WittLaw.addFam p R) (v i • (X 0 : MvPowerSeries ℕ R)) =
      subst (Sum.elim (inBlk 0 fun l => v l • (X 0 : MvPowerSeries ℕ R))
        (inBlk 1 fun l => v l • (X 0 : MvPowerSeries ℕ R)))
        ((X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) + X (Sum.inr i))
    rw [subst_X_add_X h0]
    simp only [Sum.elim_inl, Sum.elim_inr, inBlk_apply]
    rw [← coe_substAlgHom (hasSubst_addFam p R), ← coe_substAlgHom (hasSubst_blk 0),
      ← coe_substAlgHom (hasSubst_blk 1), AlgHom.map_smul_of_tower, AlgHom.map_smul_of_tower,
      AlgHom.map_smul_of_tower, coe_substAlgHom, coe_substAlgHom, coe_substAlgHom,
      subst_X (hasSubst_addFam p R), subst_X (hasSubst_blk 0), subst_X (hasSubst_blk 1),
      WittLaw.addFam, WittVector.wittAdd_zero, ← smul_add]
    congr 1
    simp [WittLaw.blk]

end Examples

end CartierModule

end MvFormalGroup

end

end
