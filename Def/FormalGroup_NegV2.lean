module

public import Def.FormalGroup_EndRingV2
public import Def.FormalGroup_NegSeries
public import Theorem.MvPowerSeries.NegV2Subst

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]



namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}

def neg [IsComm G] (φ : Hom F G) : Hom F G where
  toPowerSeries := negSeries G φ.toPowerSeries
  constantCoeff_eq_zero := constantCoeff_negSeries G φ.toPowerSeries
  subst_eq := by
    intro i
    have hφ : ∀ j, (φ.toPowerSeries j).constantCoeff = 0 := φ.constantCoeff_eq_zero
    have hbF : ∀ s, (F.toPowerSeries s).constantCoeff = 0 := F.constantCoeff_eq_zero
    have hXl0 : ∀ l : Fin g,
        ((X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    have hXr0 : ∀ l : Fin g,
        ((X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    have hφL : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero hXl0) hXl0 (hφ j)
    have hφR : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero hXr0) hXr0 (hφ j)
    calc subst F.toPowerSeries (negSeries G φ.toPowerSeries i)
        = negSeries G (fun j => subst F.toPowerSeries (φ.toPowerSeries j)) i :=
          congrFun (subst_negSeries G hφ hbF) i
      _ = negSeries G (fun j => subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j')) (G.toPowerSeries j)) i := by
          have hc : (fun j => subst F.toPowerSeries (φ.toPowerSeries j))
              = fun j => subst (Sum.elim
                (fun j' => subst
                  (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                  (φ.toPowerSeries j'))
                fun j' => subst
                  (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                  (φ.toPowerSeries j')) (G.toPowerSeries j) := by
            funext j
            exact φ.subst_eq j
          rw [hc]
      _ = subst (Sum.elim
            (negSeries G fun j' => subst
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            (negSeries G fun j' => subst
              (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))) (G.toPowerSeries i) :=
          congrFun (negSeries_elim_add G hφL hφR) i
      _ = subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (negSeries G φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (negSeries G φ.toPowerSeries j') ) (G.toPowerSeries i) := by
          rw [← subst_negSeries G hφ hXl0, ← subst_negSeries G hφ hXr0]

end Hom

end MvFormalGroup

end

end
