module

public import Mathlib
public import Structure.MvFormalGroup_CartierModule
public import Theorem.MvPowerSeries.CartierModuleSubst
public import Def.FormalGroup_CartierModuleInBlk

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup


open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]


namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}


@[simp] public theorem inBlk_apply (i : Fin 2) (a : Fin d → MvPowerSeries ℕ R) (l : Fin d) :
    inBlk i a l = subst (blk i) (a l) := rfl


omit hp in

public theorem constantCoeff_inBlk (i : Fin 2) {a : Fin d → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) (l : Fin d) : (inBlk i a l).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_blk i) (constantCoeff_blk i) (ha l)


omit hp in

public theorem inBlk_zero (i : Fin 2) : inBlk i (fun _ : Fin d => (0 : MvPowerSeries ℕ R)) = fun _ => 0 := by
  funext l
  show subst (blk i) (0 : MvPowerSeries ℕ R) = 0
  rw [← coe_substAlgHom (hasSubst_blk i), map_zero]


omit hp in


public theorem inBlk_subst_elim (G : MvFormalGroup d' R) (i : Fin 2) {a b : Fin d' → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) (hb : ∀ l, (b l).constantCoeff = 0) :
    inBlk i (fun l => subst (Sum.elim a b) (G.toPowerSeries l)) =
      fun l => subst (Sum.elim (inBlk i a) (inBlk i b)) (G.toPowerSeries l) := by
  funext l
  exact subst_subst_elim G ha hb (hasSubst_blk i) l


omit hp in


public theorem inBlk_negSeries (G : MvFormalGroup d' R) (i : Fin 2) {a : Fin d' → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) :
    inBlk i (negSeries G a) = negSeries G (inBlk i a) := by
  have hneg : ∀ j, (negSeries G a j).constantCoeff = 0 := constantCoeff_negSeries G a
  refine negSeries_unique G (constantCoeff_inBlk i ha) (constantCoeff_inBlk i hneg) fun l => ?_
  have h := congrFun (inBlk_subst_elim G i ha hneg) l
  rw [← h]
  show subst (blk i) (subst (Sum.elim a (negSeries G a)) (G.toPowerSeries l)) = 0
  rw [subst_elim_negSeries G ha l, ← coe_substAlgHom (hasSubst_blk i), map_zero]


public theorem subst_addFam (f : CartierModule p Φ) (j : Fin d) :
    subst (WittLaw.addFam p R) (f.toPowerSeries j) =
      subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries)) (Φ.toPowerSeries j) :=
  f.subst_eq j

end CartierModule

namespace WittLaw

variable (p)


variable {p}

variable (R)


omit hp in

public theorem constantCoeff_verFam (n : ℕ) : (verFam R n).constantCoeff = 0 := by
  cases n with
  | zero => exact map_zero _
  | succ n => exact constantCoeff_X _

omit hp in

public theorem hasSubst_verFam : HasSubst (verFam R) := by
  classical
  refine ⟨fun n => by rw [constantCoeff_verFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (e.support.image Nat.succ).finite_toSet.subset fun n hn => ?_
  cases n with
  | zero => exact absurd (by simp [verFam]) hn
  | succ n =>
    have h : coeff e (X n : MvPowerSeries ℕ R) ≠ 0 := hn
    rw [coeff_X] at h
    split_ifs at h with he
    · subst he
      simp
    · exact absurd rfl h

public theorem isEndo_verFam : IsEndo p (verFam R) := by
  refine ⟨hasSubst_verFam R, constantCoeff_verFam R, fun n => ?_⟩
  have hpair : pairFam (verFam R) = fun im : Fin 2 × ℕ =>
      ((MvPolynomial.map (Int.castRingHom R)
        (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ) :
          MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    funext ⟨i, m⟩
    cases m with
    | zero =>
      show subst (blk i) (0 : MvPowerSeries ℕ R) = _
      rw [← coe_substAlgHom (hasSubst_blk i), map_zero]
      simp
    | succ m =>
      show subst (blk i) (X m : MvPowerSeries ℕ R) = _
      rw [subst_X (hasSubst_blk i)]
      simp [blk]
  rw [hpair, subst_coe_addFam (p := p) (R := R) (τ := Fin 2 × ℕ) (g := fun im : Fin 2 × ℕ =>
    (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ)) (n := n),
    aeval_verschiebung_wittAdd]
  cases n with
  | zero =>
    show subst (addFam p R) (0 : MvPowerSeries ℕ R) = _
    rw [← coe_substAlgHom (hasSubst_addFam p R), map_zero]
    simp
  | succ m =>
    show subst (addFam p R) (X m : MvPowerSeries ℕ R) = _
    rw [subst_X (hasSubst_addFam p R)]
    rfl

omit hp in

@[simp] public theorem frobFam_apply (n : ℕ) : frobFam p R n = X n ^ p := rfl

public theorem constantCoeff_frobFam (n : ℕ) : (frobFam p R n).constantCoeff = 0 := by
  rw [frobFam_apply, map_pow, constantCoeff_X, zero_pow hp.out.ne_zero]

public theorem hasSubst_frobFam : HasSubst (frobFam p R) := HasSubst.X_pow hp.out.ne_zero

public theorem isEndo_frobFam [CharP R p] : IsEndo p (frobFam p R) := by
  refine ⟨hasSubst_frobFam R, constantCoeff_frobFam R, fun n => ?_⟩
  have hpair : pairFam (frobFam p R) = fun im : Fin 2 × ℕ =>
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.X im ^ p : MvPolynomial (Fin 2 × ℕ) ℤ) :
        MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    funext ⟨i, m⟩
    show subst (blk i) (X m ^ p : MvPowerSeries ℕ R) = _
    rw [subst_pow (hasSubst_blk i), subst_X (hasSubst_blk i), map_pow, MvPolynomial.map_X,
      MvPolynomial.coe_pow, MvPolynomial.coe_X]
    rfl
  rw [hpair, frobFam_apply, subst_pow (hasSubst_addFam p R), subst_X (hasSubst_addFam p R),
    subst_coe_addFam (p := p) (R := R) (τ := Fin 2 × ℕ) (g := fun im : Fin 2 × ℕ => (MvPolynomial.X im ^ p : MvPolynomial (Fin 2 × ℕ) ℤ)) (n := n)]
  have hexp : MvPolynomial.aeval (fun im : Fin 2 × ℕ => (MvPolynomial.X im ^ p :
      MvPolynomial (Fin 2 × ℕ) ℤ)) (WittVector.wittAdd p n) =
      MvPolynomial.expand p (WittVector.wittAdd p n) := by
    rw [MvPolynomial.expand, ← MvPolynomial.aeval_eq_bind₁]
  rw [hexp, MvPolynomial.map_expand, expand_map_wittAdd, MvPolynomial.coe_pow]
  rfl

end WittLaw

end MvFormalGroup

end
