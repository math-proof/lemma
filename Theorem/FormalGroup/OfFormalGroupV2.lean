module

public import Class.MvFormalGroup_BasicV2
public import Theorem.FormalGroup.NSeries
public import Def.FormalGroup_PointTransport
public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Instance.MvFormalGroup_OfFormalGroupV2

public noncomputable section

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {R : Type*} [CommRing R]


@[simp] public theorem e2_zero : e2 0 = Sum.inl 0 := rfl


@[simp] public theorem e2_one : e2 1 = Sum.inr 0 := rfl


@[simp] public theorem e3_zero : e3 0 = Sum.inl 0 := rfl


@[simp] public theorem e3_one : e3 1 = Sum.inr (Sum.inl 0) := rfl


@[simp] public theorem e3_two : e3 2 = Sum.inr (Sum.inr 0) := rfl


public theorem subst_rename {σ τ υ : Type*} (e : σ ↪ τ) {a : τ → MvPowerSeries υ R}
    (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (rename e f) = subst (fun s => a (e s)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) ha]
  congr 1
  funext s
  exact subst_X ha (e s)


public theorem rename_subst {σ τ υ : Type*} (e : τ ↪ υ) {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (f : MvPowerSeries σ R) :
    rename e (subst a f) = subst (fun s => rename e (a s)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply ha (HasSubst.X_comp _)]
  congr 1
  funext s
  exact (rename_eq_subst _ (a s)).symm


public theorem coeff_ofFormalGroup (F : FormalGroup R) (a b : ℕ) (i : Fin 1) :
    coeff (Finsupp.single (Sum.inl 0) a + Finsupp.single (Sum.inr 0) b)
        ((ofFormalGroup F).toPowerSeries i)
      = coeff (Finsupp.single 0 a + Finsupp.single 1 b) F.toPowerSeries := by
  rw [show Finsupp.single (Sum.inl (0 : Fin 1)) a + Finsupp.single (Sum.inr (0 : Fin 1)) b
      = Finsupp.embDomain e2 (Finsupp.single 0 a + Finsupp.single 1 b) by
    rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]; rfl]
  exact coeff_embDomain_rename e2 F.toPowerSeries _


public theorem eq_of_toPowerSeries_eq {g : ℕ} : ∀ {F G : MvFormalGroup g R}, F.toPowerSeries = G.toPowerSeries → F = G
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, rfl => rfl


@[simp] public theorem e1_apply (u : Unit) : e1 u = 0 := rfl


public theorem toMv_def (s : PowerSeries R) : toMv s = rename e1 s := rfl


public theorem ofMv_toMv (s : PowerSeries R) : ofMv (toMv s) = s := killCompl_rename_app s


public theorem single_zero_eq_embDomain (n : ℕ) :
    Finsupp.single (0 : Fin 1) n = Finsupp.embDomain e1 (Finsupp.single () n) := by
  rw [Finsupp.embDomain_single]; rfl


public theorem coeff_toMv (s : PowerSeries R) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) (toMv s) = PowerSeries.coeff n s := by
  rw [toMv, single_zero_eq_embDomain, coeff_embDomain_rename]; rfl


public theorem toMv_ofMv (t : MvPowerSeries (Fin 1) R) : toMv (ofMv t) = t := by
  ext x
  obtain ⟨n, rfl⟩ : ∃ n, x = Finsupp.single 0 n := ⟨x 0, Finsupp.unique_single x⟩
  rw [coeff_toMv, ofMv, PowerSeries.coeff, coeff_killCompl, ← single_zero_eq_embDomain]


public theorem toMv_injective : Function.Injective (toMv (R := R)) :=
  fun s t h => by rw [← ofMv_toMv s, ← ofMv_toMv t, h]


public theorem constantCoeff_toMv (s : PowerSeries R) :
    MvPowerSeries.constantCoeff (toMv s) = PowerSeries.constantCoeff s := by
  rw [toMv, constantCoeff_rename]; rfl


public theorem toMv_X : toMv (PowerSeries.X : PowerSeries R) = X 0 := by
  rw [toMv, show (PowerSeries.X : PowerSeries R) = X () from rfl, rename_X]; rfl


public theorem toMv_zero : toMv (0 : PowerSeries R) = 0 := map_zero _


public theorem hasSubst_toMv {s : PowerSeries R} (hs : PowerSeries.constantCoeff s = 0) :
    HasSubst (fun _ : Fin 1 => toMv s) :=
  hasSubst_of_constantCoeff_zero fun _ => by rw [constantCoeff_toMv, hs]


public theorem linearPart_toMv (s : PowerSeries R) :
    linearPart (fun _ : Fin 1 => toMv s) = PowerSeries.coeff 1 s • (1 : Matrix (Fin 1) (Fin 1) R) := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [linearPart, coeff_toMv]


public theorem ofFormalGroup_eq_map_of_isBaseChange {S : Type*} [CommRing S] (F : FormalGroup R) (f : R →+* S)
    (G : FormalGroup S) (h : F.IsBaseChange f G) :
    ofFormalGroup G = (ofFormalGroup F).map f := by
  apply eq_of_toPowerSeries_eq
  funext i
  show rename e2 G.toPowerSeries = MvPowerSeries.map f (rename e2 F.toPowerSeries)
  unfold FormalGroup.IsBaseChange at h
  rw [h, rename_map]


public theorem ofFormalGroup_map {S : Type*} [CommRing S] (F : FormalGroup R) (f : R →+* S) :
    ofFormalGroup (F.map f) = (ofFormalGroup F).map f :=
  ofFormalGroup_eq_map_of_isBaseChange F f (F.map f) rfl

omit [CommRing R] in


public theorem sumElim_comp_e2 {R : Type*} [Semiring R] {τ : Type*} (a b : MvPowerSeries τ R) :
    (fun s : Fin 2 => Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) (e2 s)) = ![a, b] := by
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero]
  · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero]


public theorem nthSeries_ofFormalGroup (F : FormalGroup R) (n : ℕ) :
    (ofFormalGroup F).nthSeries n = fun _ => toMv (F.nthSeries n) := by
  induction n with
  | zero => funext i; rw [MvFormalGroup.nthSeries_zero, FormalGroup.nthSeries_zero, toMv_zero]
  | succ n ih =>
    funext i
    rw [MvFormalGroup.nthSeries_succ, ih, FormalGroup.nthSeries_succ]
    have hfam : HasSubst (Sum.elim (fun _ : Fin 1 => toMv (F.nthSeries n))
        (fun j : Fin 1 => (X j : MvPowerSeries (Fin 1) R))) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · rw [Sum.elim_inl, constantCoeff_toMv]; exact F.constantCoeff_nthSeries n
      · exact constantCoeff_X _
    show subst (Sum.elim (fun _ : Fin 1 => toMv (F.nthSeries n)) fun j => X j) (rename e2 F.toPowerSeries) =
      rename e1 (subst ![F.nthSeries n, PowerSeries.X] F.toPowerSeries)
    rw [subst_rename e2 hfam, rename_subst e1 (F.hasSubst_nthSeries n)]
    congr 1
    refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero]; rfl
    · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero,
        show (PowerSeries.X : PowerSeries R) = X () from rfl, rename_X]; rfl


public theorem rename_e2_lawHom_lhs (F : FormalGroup R) (s : PowerSeries R) (_hs : PowerSeries.constantCoeff s = 0) :
    rename e2 (PowerSeries.subst F.toPowerSeries s) =
      subst (ofFormalGroup F).toPowerSeries (toMv s) := by
  show rename e2 (subst (fun _ : Unit => F.toPowerSeries) s) =
    subst (fun _ : Fin 1 => rename e2 F.toPowerSeries) (rename e1 s)
  rw [rename_subst e2 (hasSubst_of_constantCoeff_zero fun _ => F.zero_constantCoeff),
    subst_rename e1 (hasSubst_of_constantCoeff_zero fun _ => by
      rw [constantCoeff_rename]; exact F.zero_constantCoeff)]


public theorem rename_e2_lawHom_rhs (G : FormalGroup R) (s : PowerSeries R) (hs : PowerSeries.constantCoeff s = 0) :
    rename e2 (MvPowerSeries.subst ![FormalGroup.LawHom.substX 0 s, FormalGroup.LawHom.substX 1 s] G.toPowerSeries) =
      subst (Sum.elim
        (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s))
        (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s)))
        ((ofFormalGroup G).toPowerSeries 0) := by
  have hsX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (FormalGroup.LawHom.substX i s) = 0 := by
    intro i
    unfold FormalGroup.LawHom.substX
    exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) s hs
  have hL : HasSubst (![FormalGroup.LawHom.substX 0 s, FormalGroup.LawHom.substX 1 s] :
      Fin 2 → MvPowerSeries (Fin 2) R) :=
    hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨hsX 0, hsX 1⟩)
  have hcs : ∀ (b : Bool), MvPowerSeries.constantCoeff
      (subst (fun l : Fin 1 => (X (cond b (Sum.inl l) (Sum.inr l)) : MvPowerSeries (Fin 1 ⊕ Fin 1) R))
        (toMv s)) = 0 := by
    intro b
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (by rw [constantCoeff_toMv, hs])
  have hR : HasSubst (Sum.elim
      (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s))
      (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s))) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact hcs true
    · exact hcs false
  show rename e2 (subst ![FormalGroup.LawHom.substX 0 s, FormalGroup.LawHom.substX 1 s] G.toPowerSeries) =
    subst _ (rename e2 G.toPowerSeries)
  rw [rename_subst e2 hL, subst_rename e2 hR]
  congr 1
  have key : ∀ (i : Fin 2) (c : Fin 1 → Fin 1 ⊕ Fin 1), c 0 = e2 i →
      rename e2 (FormalGroup.LawHom.substX i s) =
        subst (fun l : Fin 1 => (X (c l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s) := by
    intro i c hc
    unfold FormalGroup.LawHom.substX
    show rename e2 (subst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) R)) s) =
      subst (fun l : Fin 1 => (X (c l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (rename e1 s)
    rw [rename_subst e2 (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
      subst_rename e1 (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    congr 1
    funext u
    rw [rename_X, e1_apply, hc]
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero]
    exact key 0 _ (e2_zero).symm
  · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact key 1 _ (e2_one).symm


public theorem lawHom_comm_iff (F G : FormalGroup R) (s : PowerSeries R) (hs : PowerSeries.constantCoeff s = 0) :
    PowerSeries.subst F.toPowerSeries s =
        MvPowerSeries.subst ![FormalGroup.LawHom.substX 0 s, FormalGroup.LawHom.substX 1 s] G.toPowerSeries ↔
      ∀ i : Fin 1, subst (ofFormalGroup F).toPowerSeries (toMv s) =
        subst (Sum.elim
          (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s))
          (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s)))
          ((ofFormalGroup G).toPowerSeries i) := by
  constructor
  · intro h i
    rw [Subsingleton.elim i 0, ← rename_e2_lawHom_lhs F s hs, ← rename_e2_lawHom_rhs G s hs, h]
  · intro h
    apply rename_injective (R := R) e2
    rw [rename_e2_lawHom_lhs F s hs, rename_e2_lawHom_rhs G s hs]
    exact h 0


@[simp] public theorem _root_.FormalGroup.LawHom.toMvHom_toPowerSeries {F G : FormalGroup R}
    (θ : FormalGroup.LawHom F G) (i : Fin 1) : θ.toMvHom.toPowerSeries i = toMv θ.series := rfl


@[simp] public theorem _root_.FormalGroup.LawHom.ofMvHom_series {F G : FormalGroup R}
    (f : Hom (ofFormalGroup F) (ofFormalGroup G)) : (FormalGroup.LawHom.ofMvHom f).series = ofMv (f.toPowerSeries 0) :=
  rfl

end MvFormalGroup

end
