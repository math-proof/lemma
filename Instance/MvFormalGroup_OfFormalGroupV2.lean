-- Carved from Lemma/Definitions/Def_MvFormalGroup_OfFormalGroupV2.lean: instance decls only.
import Class.MvFormalGroup_BasicV2
import Lemma.FormalGroup.NSeries
import Def.FormalGroup_PointTransport
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename
import Lemma.MvFormalGroup.OfFormalGroupV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {R : Type*} [CommRing R]

instance instIsCommOfFormalGroup (F : FormalGroup R) [F.IsComm] : (ofFormalGroup F).IsComm where
  comm := by
    intro i
    show subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) R))
        fun j => X (Sum.inl j)) (rename e2 F.toPowerSeries) = rename e2 F.toPowerSeries
    have hs : HasSubst (Sum.elim
        (fun j : Fin 1 => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) R))
        fun j => X (Sum.inl j)) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with l | l <;> simp
    rw [subst_rename e2 hs]
    calc subst (fun s => Sum.elim
            (fun j : Fin 1 => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) R))
            (fun j => X (Sum.inl j)) (e2 s)) F.toPowerSeries
        = subst (fun s => rename e2 ((![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) R) s))
            F.toPowerSeries := by
          refine congrArg (fun a => subst a F.toPowerSeries) ?_
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
          · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero, rename_X, e2_one]
          · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, rename_X,
              e2_zero]
      _ = rename e2 (subst ![X 1, X 0] F.toPowerSeries) :=
          (rename_subst e2 HasSubst.X_X F.toPowerSeries).symm
      _ = rename e2 F.toPowerSeries :=
          congrArg (rename e2) (FormalGroup.IsComm.comm (F := F)).symm

end MvFormalGroup

end
