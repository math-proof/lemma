module

public import Class.MvFormalGroup_BasicV2
public import Theorem.MvPowerSeries.EndRingV2Subst

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]


namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}

def zero (F : MvFormalGroup g R) (G : MvFormalGroup h R) : Hom F G where
  toPowerSeries := fun _ => 0
  constantCoeff_eq_zero := fun _ => map_zero _
  subst_eq := by
    intro i
    have hXl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hXr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    show subst F.toPowerSeries (0 : MvPowerSeries (Fin g) R)
      = subst (Sum.elim
          (fun _ : Fin h => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R))
          fun _ : Fin h => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R))
        (G.toPowerSeries i)
    have hL : subst F.toPowerSeries (0 : MvPowerSeries (Fin g) R) = 0 := by
      rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero), map_zero]
    have hfam : (Sum.elim
        (fun _ : Fin h => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (0 : MvPowerSeries (Fin g) R))
        fun _ : Fin h => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (0 : MvPowerSeries (Fin g) R))
        = fun _ : Fin h ⊕ Fin h => (0 : MvPowerSeries (Fin g ⊕ Fin g) R) := by
      funext s
      rcases s with j | j
      · show subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R) = 0
        rw [← coe_substAlgHom hXl, map_zero]
      · show subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R) = 0
        rw [← coe_substAlgHom hXr, map_zero]
    rw [hL, hfam,
      subst_zero_of_constantCoeff_eq_zero (G.constantCoeff_eq_zero i)]

def add [IsComm G] (φ ψ : Hom F G) : Hom F G where
  toPowerSeries := fun i =>
    subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries i)
  constantCoeff_eq_zero := fun i =>
    constantCoeff_subst_elim G φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero i
  subst_eq := by
    intro i
    have hXl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hXr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hφψ : HasSubst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) :=
      hasSubst_elim φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero
    have hφL : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j)
    have hφR : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j)
    have hψL : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (ψ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (ψ.constantCoeff_eq_zero j)
    have hψR : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (ψ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (ψ.constantCoeff_eq_zero j)
    show subst F.toPowerSeries
        (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries i))
      = subst (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)))
        (G.toPowerSeries i)
    rw [subst_comp_subst_apply hφψ (hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero)]
    have hLfam : (fun s => subst F.toPowerSeries
        ((Sum.elim φ.toPowerSeries ψ.toPowerSeries) s))
        = Sum.elim (fun j => subst F.toPowerSeries (φ.toPowerSeries j))
          fun j => subst F.toPowerSeries (ψ.toPowerSeries j) := by
      funext s
      rcases s with j | j <;> rfl
    rw [hLfam]
    have hφeq : (fun j => subst F.toPowerSeries (φ.toPowerSeries j))
        = fun j => subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j')) (G.toPowerSeries j) :=
      funext fun j => φ.subst_eq j
    have hψeq : (fun j => subst F.toPowerSeries (ψ.toPowerSeries j))
        = fun j => subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j')) (G.toPowerSeries j) :=
      funext fun j => ψ.subst_eq j
    rw [hφeq, hψeq, subst_elim_exchange G hφL hφR hψL hψR i]
    have hfinL : (fun s' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        ((Sum.elim φ.toPowerSeries ψ.toPowerSeries) s'))
        = Sum.elim (fun j' => subst
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j') := by
      funext s'
      rcases s' with j' | j' <;> rfl
    have hfinR : (fun s' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        ((Sum.elim φ.toPowerSeries ψ.toPowerSeries) s'))
        = Sum.elim (fun j' => subst
            (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j') := by
      funext s'
      rcases s' with j' | j' <;> rfl
    have hfinal : (Sum.elim
        (fun j => subst (Sum.elim
          (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j')) (G.toPowerSeries j))
        fun j => subst (Sum.elim
          (fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j')) (G.toPowerSeries j))
        = Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)) := by
      funext s
      rcases s with j | j
      · show subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j')) (G.toPowerSeries j)
          = subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j))
        rw [subst_comp_subst_apply hφψ hXl, hfinL]
      · show subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j')) (G.toPowerSeries j)
          = subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j))
        rw [subst_comp_subst_apply hφψ hXr, hfinR]
    rw [hfinal]

end Hom

end MvFormalGroup

end

end
