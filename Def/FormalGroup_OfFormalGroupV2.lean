import Class.MvFormalGroup_BasicV2
import Theorem.FormalGroup.NSeries
import Def.FormalGroup_PointTransport
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename
import Instance.MvFormalGroup_OfFormalGroupV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {R : Type*} [CommRing R]

def e2 : Fin 2 ↪ Fin 1 ⊕ Fin 1 :=
  ⟨![Sum.inl 0, Sum.inr 0], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def e3 : Fin 3 ↪ Fin 1 ⊕ (Fin 1 ⊕ Fin 1) :=
  ⟨![Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inr (Sum.inr 0)], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def ofFormalGroup (F : FormalGroup R) : MvFormalGroup 1 R where
  toPowerSeries := fun _ => rename e2 F.toPowerSeries
  constantCoeff_eq_zero := fun _ => by rw [constantCoeff_rename, F.zero_constantCoeff]
  coeff_single_inl := by
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0, if_pos rfl,
      show Finsupp.single (Sum.inl (0 : Fin 1)) 1 = Finsupp.embDomain e2 (Finsupp.single 0 1) by
        rw [Finsupp.embDomain_single]; rfl,
      coeff_embDomain_rename]
    exact F.lin_coeff_X
  coeff_single_inr := by
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0, if_pos rfl,
      show Finsupp.single (Sum.inr (0 : Fin 1)) 1 = Finsupp.embDomain e2 (Finsupp.single 1 1) by
        rw [Finsupp.embDomain_single]; rfl,
      coeff_embDomain_rename]
    exact F.lin_coeff_Y
  assoc := by
    intro i

    have c0 : ∀ a b : Fin 3, MvPowerSeries.constantCoeff
        (subst (![X a, X b] : Fin 2 → MvPowerSeries (Fin 3) R) F.toPowerSeries) = 0 :=
      fun a b => constantCoeff_subst_eq_zero HasSubst.X_X
        (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩) F.zero_constantCoeff
    have hL : HasSubst (![subst ![X 0, X 1] F.toPowerSeries, X 2] :
        Fin 2 → MvPowerSeries (Fin 3) R) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨c0 0 1, constantCoeff_X _⟩)
    have hR : HasSubst (![X 0, subst ![X 1, X 2] F.toPowerSeries] :
        Fin 2 → MvPowerSeries (Fin 3) R) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, c0 1 2⟩)

    have hB : HasSubst (Sum.elim
        (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        fun l => X (Sum.inr (Sum.inl l))) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with l | l <;> simp
    have hC : HasSubst (Sum.elim
        (fun l : Fin 1 => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        fun l => X (Sum.inr (Sum.inr l))) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with l | l <;> simp
    have hB2 : HasSubst (fun s : Fin 2 => Sum.elim
        (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        (fun l => X (Sum.inr (Sum.inl l))) (e2 s)) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩)
    have hC2 : HasSubst (fun s : Fin 2 => Sum.elim
        (fun l : Fin 1 => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        (fun l => X (Sum.inr (Sum.inr l))) (e2 s)) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩)
    rw [subst_rename e2 hB, subst_rename e2 hC]
    have hA₁ : HasSubst (Sum.elim
        (fun _ : Fin 1 => subst (fun s : Fin 2 => Sum.elim
          (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
          (fun l => X (Sum.inr (Sum.inl l))) (e2 s)) F.toPowerSeries)
        fun j => X (Sum.inr (Sum.inr j))) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero hB2
          (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩) F.zero_constantCoeff
      · exact constantCoeff_X _
    have hA₂ : HasSubst (Sum.elim
        (fun j : Fin 1 => (X (Sum.inl j) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        fun _ : Fin 1 => subst (fun s : Fin 2 => Sum.elim
          (fun l : Fin 1 => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
          (fun l => X (Sum.inr (Sum.inr l))) (e2 s)) F.toPowerSeries) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_eq_zero hC2
          (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩) F.zero_constantCoeff
    rw [subst_rename e2 hA₁, subst_rename e2 hA₂]

    have eL : (fun s : Fin 2 => Sum.elim
        (fun _ : Fin 1 => subst (fun s : Fin 2 => Sum.elim
          (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
          (fun l => X (Sum.inr (Sum.inl l))) (e2 s)) F.toPowerSeries)
        (fun j => X (Sum.inr (Sum.inr j))) (e2 s))
        = fun s => rename e3 ((![subst ![X 0, X 1] F.toPowerSeries, X 2] :
            Fin 2 → MvPowerSeries (Fin 3) R) s) := by
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero, rename_subst _ HasSubst.X_X]
        refine congrArg (fun a => subst a F.toPowerSeries) ?_
        refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
        · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero, rename_X, e3_zero]
        · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, rename_X, e3_one]
      · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, rename_X, e3_two]
    have eR : (fun s : Fin 2 => Sum.elim
        (fun j : Fin 1 => (X (Sum.inl j) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        (fun _ => subst (fun s : Fin 2 => Sum.elim
          (fun l : Fin 1 => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
          (fun l => X (Sum.inr (Sum.inr l))) (e2 s)) F.toPowerSeries) (e2 s))
        = fun s => rename e3 ((![X 0, subst ![X 1, X 2] F.toPowerSeries] :
            Fin 2 → MvPowerSeries (Fin 3) R) s) := by
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero, rename_X, e3_zero]
      · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero,
          rename_subst _ HasSubst.X_X]
        refine congrArg (fun a => subst a F.toPowerSeries) ?_
        refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
        · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero, rename_X, e3_one]
        · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, rename_X, e3_two]
    rw [eL, eR, ← rename_subst e3 hL, ← rename_subst e3 hR]
    exact congrArg (rename e3) F.assoc

def e1 : Unit ↪ Fin 1 := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

def toMv (s : PowerSeries R) : MvPowerSeries (Fin 1) R := rename e1 s

def ofMv (t : MvPowerSeries (Fin 1) R) : PowerSeries R := killCompl e1 t

def _root_.FormalGroup.LawHom.toMvHom {F G : FormalGroup R} (θ : FormalGroup.LawHom F G) :
    Hom (ofFormalGroup F) (ofFormalGroup G) where
  toPowerSeries := fun _ => toMv θ.series
  constantCoeff_eq_zero := fun _ => by rw [constantCoeff_toMv]; exact θ.constantCoeff_series
  subst_eq := (lawHom_comm_iff F G θ.series θ.constantCoeff_series).mp θ.comm

def _root_.FormalGroup.LawHom.ofMvHom {F G : FormalGroup R} (f : Hom (ofFormalGroup F) (ofFormalGroup G)) :
    FormalGroup.LawHom F G where
  series := ofMv (f.toPowerSeries 0)
  constantCoeff_series := by
    rw [← constantCoeff_toMv, toMv_ofMv]; exact f.constantCoeff_eq_zero 0
  comm := by
    have hs : PowerSeries.constantCoeff (ofMv (f.toPowerSeries 0)) = 0 := by
      rw [← constantCoeff_toMv, toMv_ofMv]; exact f.constantCoeff_eq_zero 0
    refine (lawHom_comm_iff F G _ hs).mpr fun i => ?_
    have key := f.subst_eq i
    have h0 : ∀ j : Fin 1, f.toPowerSeries j = f.toPowerSeries 0 := fun j => by
      rw [Subsingleton.elim j 0]
    simp only [h0] at key
    rw [toMv_ofMv]
    exact key

end MvFormalGroup

end
