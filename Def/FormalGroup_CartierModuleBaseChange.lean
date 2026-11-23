import Mathlib
import Def.FormalGroup_NegV2
import Def.FormalGroup_CartierModule
import Def.PowerSeries_CartierModuleHomothety
import Def.FormalGroup_CartierModuleWittAction

set_option autoImplicit false

noncomputable section

universe u v w

open MvPowerSeries

namespace MvFormalGroup

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ}
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {T : Type w} [CommRing T]

omit hp in

namespace WittLaw

omit hp in

end WittLaw

namespace CartierModule

open WittLaw

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}
variable {Ψ : MvFormalGroup d S} {Ψ' : MvFormalGroup d' S}

omit hp in

def baseChangeEqFun (f : R →+* S) (h : Φ.map f = Ψ) (m : CartierModule p Φ) : CartierModule p Ψ where
  toPowerSeries := fun j => MvPowerSeries.map f (m.toPowerSeries j)
  constantCoeff_eq_zero := fun j => constantCoeff_map_family m.constantCoeff_eq_zero f j
  subst_eq := by
    intro j
    subst h
    have hm := m.constantCoeff_eq_zero
    have hm' : ∀ l, (MvPowerSeries.map f (m.toPowerSeries l)).constantCoeff = 0 :=
      constantCoeff_map_family hm f
    have key := congrArg (MvPowerSeries.map f) (m.subst_addFam j)
    have hE : HasSubst (Sum.elim (inBlk 0 m.toPowerSeries) (inBlk 1 m.toPowerSeries)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (l | l)
      · exact constantCoeff_inBlk 0 hm l
      · exact constantCoeff_inBlk 1 hm l
    rw [map_subst (hasSubst_addFam p R), map_subst hE] at key
    have hA : (fun n => MvPowerSeries.map f (addFam p R n)) = addFam p S := funext (map_addFam f)
    rw [hA] at key
    have hblk : ∀ (i : Fin 2) (l : Fin d), MvPowerSeries.map f (inBlk i m.toPowerSeries l) =
        inBlk i (fun l => MvPowerSeries.map f (m.toPowerSeries l)) l := by
      intro i l
      rw [inBlk_apply, inBlk_apply, map_subst (hasSubst_blk i)]
      congr 1
      funext n
      exact map_X f (i, n)
    have hfam : (fun s => MvPowerSeries.map f
        (Sum.elim (inBlk 0 m.toPowerSeries) (inBlk 1 m.toPowerSeries) s)) =
        Sum.elim (inBlk 0 fun l => MvPowerSeries.map f (m.toPowerSeries l))
          (inBlk 1 fun l => MvPowerSeries.map f (m.toPowerSeries l)) := by
      funext s
      rcases s with l | l
      · exact hblk 0 l
      · exact hblk 1 l
    rw [hfam] at key
    exact key

def baseChangeEq [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ) :
    CartierModule p Φ →+ CartierModule p Ψ where
  toFun := baseChangeEqFun f h
  map_zero' := CartierModule.ext (funext fun j => by
    show MvPowerSeries.map f 0 = 0
    exact map_zero _)
  map_add' m m' := CartierModule.ext (funext fun j => by
    show MvPowerSeries.map f (subst (Sum.elim m.toPowerSeries m'.toPowerSeries) (Φ.toPowerSeries j)) =
      subst (Sum.elim (fun l => MvPowerSeries.map f (m.toPowerSeries l))
        fun l => MvPowerSeries.map f (m'.toPowerSeries l)) (Ψ.toPowerSeries j)
    have hS : HasSubst (Sum.elim m.toPowerSeries m'.toPowerSeries) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (l | l)
      · exact m.constantCoeff_eq_zero l
      · exact m'.constantCoeff_eq_zero l
    rw [map_subst hS, map_sumElim, ← h]
    rfl)

abbrev baseChange [Φ.IsComm] (f : R →+* S) : CartierModule p Φ →+ CartierModule p (Φ.map f) :=
  baseChangeEq f rfl


end CartierModule

end MvFormalGroup

end
