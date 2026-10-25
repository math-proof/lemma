-- Carved from Lemma/Definitions/Def_MvFormalGroup_EndRingV2.lean: instance decls only.
import Class.MvFormalGroup_BasicV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]


namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}


instance instZero : Zero (Hom F G) := ⟨Hom.zero F G⟩


instance instAdd [IsComm G] : Add (Hom F G) := ⟨Hom.add⟩

instance instAddCommMonoid [IsComm G] : AddCommMonoid (Hom F G) where
  add := (· + ·)
  zero := 0
  nsmul := nsmulRec
  add_assoc a b c := by
    apply Hom.ext
    funext i
    show subst (Sum.elim
        (fun j => subst (Sum.elim a.toPowerSeries b.toPowerSeries) (G.toPowerSeries j))
        c.toPowerSeries) (G.toPowerSeries i)
      = subst (Sum.elim a.toPowerSeries
        fun j => subst (Sum.elim b.toPowerSeries c.toPowerSeries) (G.toPowerSeries j))
        (G.toPowerSeries i)
    exact subst_elim_assoc G a.constantCoeff_eq_zero b.constantCoeff_eq_zero
      c.constantCoeff_eq_zero i
  zero_add a := by
    apply Hom.ext
    funext i
    show subst (Sum.elim (fun _ => 0) a.toPowerSeries) (G.toPowerSeries i)
      = a.toPowerSeries i
    have hsa : HasSubst a.toPowerSeries := a.hasSubst_toPowerSeries
    have h0X : HasSubst (Sum.elim (fun _ : Fin h => (0 : MvPowerSeries (Fin h) R))
        fun j => (X j : MvPowerSeries (Fin h) R)) :=
      hasSubst_elim (fun _ => map_zero _) fun j => constantCoeff_X j
    have hfam : (fun s => subst a.toPowerSeries
        ((Sum.elim (fun _ : Fin h => (0 : MvPowerSeries (Fin h) R))
          fun j => (X j : MvPowerSeries (Fin h) R)) s))
        = Sum.elim (fun _ : Fin h => (0 : MvPowerSeries (Fin g) R)) a.toPowerSeries := by
      funext s
      rcases s with j | j
      · show subst a.toPowerSeries (0 : MvPowerSeries (Fin h) R) = 0
        rw [← coe_substAlgHom hsa, map_zero]
      · show subst a.toPowerSeries (X j) = a.toPowerSeries j
        exact subst_X hsa j
    have h1 : subst a.toPowerSeries (subst (Sum.elim (fun _ => 0)
        fun j => (X j : MvPowerSeries (Fin h) R)) (G.toPowerSeries i))
        = subst (Sum.elim (fun _ => 0) a.toPowerSeries) (G.toPowerSeries i) := by
      rw [subst_comp_subst_apply h0X hsa, hfam]
    rw [← h1, subst_elim_zero_X G i, subst_X hsa]
  add_zero a := by
    apply Hom.ext
    funext i
    show subst (Sum.elim a.toPowerSeries fun _ => 0) (G.toPowerSeries i)
      = a.toPowerSeries i
    have hsa : HasSubst a.toPowerSeries := a.hasSubst_toPowerSeries
    have hX0 : HasSubst (Sum.elim (fun j => (X j : MvPowerSeries (Fin h) R))
        fun _ : Fin h => (0 : MvPowerSeries (Fin h) R)) :=
      hasSubst_elim (fun j => constantCoeff_X j) fun _ => map_zero _
    have hfam : (fun s => subst a.toPowerSeries
        ((Sum.elim (fun j => (X j : MvPowerSeries (Fin h) R))
          fun _ : Fin h => (0 : MvPowerSeries (Fin h) R)) s))
        = Sum.elim a.toPowerSeries fun _ : Fin h => (0 : MvPowerSeries (Fin g) R) := by
      funext s
      rcases s with j | j
      · show subst a.toPowerSeries (X j) = a.toPowerSeries j
        exact subst_X hsa j
      · show subst a.toPowerSeries (0 : MvPowerSeries (Fin h) R) = 0
        rw [← coe_substAlgHom hsa, map_zero]
    have h1 : subst a.toPowerSeries (subst (Sum.elim
        (fun j => (X j : MvPowerSeries (Fin h) R)) fun _ => 0) (G.toPowerSeries i))
        = subst (Sum.elim a.toPowerSeries fun _ => 0) (G.toPowerSeries i) := by
      rw [subst_comp_subst_apply hX0 hsa, hfam]
    rw [← h1, subst_elim_X_zero G i, subst_X hsa]
  add_comm a b := by
    apply Hom.ext
    funext i
    show subst (Sum.elim a.toPowerSeries b.toPowerSeries) (G.toPowerSeries i)
      = subst (Sum.elim b.toPowerSeries a.toPowerSeries) (G.toPowerSeries i)
    exact subst_elim_comm G a.constantCoeff_eq_zero b.constantCoeff_eq_zero i

end Hom

namespace End

variable (F : MvFormalGroup g R)

instance instMonoid : Monoid (End F) where
  mul φ ψ := Hom.comp φ ψ
  one := Hom.id F
  mul_assoc φ ψ χ := by
    apply Hom.ext
    funext i
    show subst (Hom.toPowerSeries χ) (subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i))
      = subst (fun j => subst (Hom.toPowerSeries χ) (Hom.toPowerSeries ψ j))
        (Hom.toPowerSeries φ i)
    rw [subst_comp_subst_apply (Hom.hasSubst_toPowerSeries ψ)
      (Hom.hasSubst_toPowerSeries χ)]
  one_mul φ := by
    apply Hom.ext
    funext i
    show subst (Hom.toPowerSeries φ) (X i) = Hom.toPowerSeries φ i
    exact subst_X (Hom.hasSubst_toPowerSeries φ) i
  mul_one φ := by
    apply Hom.ext
    funext i
    show subst (fun j => (X j : MvPowerSeries (Fin g) R)) (Hom.toPowerSeries φ i)
      = Hom.toPowerSeries φ i
    exact congrFun subst_self (Hom.toPowerSeries φ i)


instance instAddCommMonoid [IsComm F] : AddCommMonoid (End F) :=
  inferInstanceAs (AddCommMonoid (Hom F F))

instance instSemiring [IsComm F] : Semiring (End F) :=
  { End.instAddCommMonoid F, End.instMonoid F with
    left_distrib := fun a b c => by
      apply Hom.ext
      funext i
      show subst (fun j => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          (F.toPowerSeries j)) (Hom.toPowerSeries a i)
        = subst (Sum.elim
            (fun j => subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
          (F.toPowerSeries i)
      have hbc : HasSubst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c)) :=
        hasSubst_elim (Hom.constantCoeff_eq_zero b) (Hom.constantCoeff_eq_zero c)
      have hXl : HasSubst (fun l : Fin g =>
          (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have hXr : HasSubst (fun l : Fin g =>
          (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have haLR : HasSubst (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (Hom.toPowerSeries a j))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (Hom.toPowerSeries a j)) :=
        hasSubst_elim
          (fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
            (Hom.constantCoeff_eq_zero a j))
          fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
            (Hom.constantCoeff_eq_zero a j)
      rw [← subst_comp_subst_apply F.hasSubst_toPowerSeries hbc, Hom.subst_eq a i,
        subst_comp_subst_apply haLR hbc]
      have hbfam : (fun l => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((fun l' => (X (Sum.inl l') : MvPowerSeries (Fin g ⊕ Fin g) R)) l))
          = Hom.toPowerSeries b := by
        funext l
        show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
            (X (Sum.inl l)) = Hom.toPowerSeries b l
        rw [subst_X hbc]
        rfl
      have hcfam : (fun l => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((fun l' => (X (Sum.inr l') : MvPowerSeries (Fin g ⊕ Fin g) R)) l))
          = Hom.toPowerSeries c := by
        funext l
        show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
            (X (Sum.inr l)) = Hom.toPowerSeries c l
        rw [subst_X hbc]
        rfl
      have hfam : (fun s => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (Hom.toPowerSeries a j))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (Hom.toPowerSeries a j)) s))
          = Sum.elim (fun j => subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j) := by
        funext s
        rcases s with j | j
        · show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
              (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (Hom.toPowerSeries a j))
            = subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j)
          rw [subst_comp_subst_apply hXl hbc, hbfam]
        · show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
              (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (Hom.toPowerSeries a j))
            = subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j)
          rw [subst_comp_subst_apply hXr hbc, hcfam]
      rw [hfam]
    right_distrib := fun a b c => by
      apply Hom.ext
      funext i
      show subst (Hom.toPowerSeries c)
          (subst (Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b))
            (F.toPowerSeries i))
        = subst (Sum.elim
            (fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries b j))
          (F.toPowerSeries i)
      have hab : HasSubst (Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b)) :=
        hasSubst_elim (Hom.constantCoeff_eq_zero a) (Hom.constantCoeff_eq_zero b)
      rw [subst_comp_subst_apply hab (Hom.hasSubst_toPowerSeries c)]
      have hfam : (fun s => subst (Hom.toPowerSeries c)
          ((Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b)) s))
          = Sum.elim (fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries b j) := by
        funext s
        rcases s with j | j <;> rfl
      rw [hfam]
    zero_mul := fun a => by
      apply Hom.ext
      funext i
      show subst (Hom.toPowerSeries a) (0 : MvPowerSeries (Fin g) R) = 0
      rw [← coe_substAlgHom (Hom.hasSubst_toPowerSeries a), map_zero]
    mul_zero := fun a => by
      apply Hom.ext
      funext i
      show subst (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
          (Hom.toPowerSeries a i) = 0
      exact subst_zero_of_constantCoeff_eq_zero (Hom.constantCoeff_eq_zero a i) }


end End


end MvFormalGroup
