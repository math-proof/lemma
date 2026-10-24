import Mathlib

set_option autoImplicit false

open MvPolynomial

namespace IncidenceSystem

inductive Var (g e m' : ℕ) : Type
  | u : Fin g → Var g e m'
  | w : Fin g → Fin e → Fin (m' + 1) → Var g e m'
  | σ : Option (Fin (g * m')) → Fin g → Fin (m' + 1) → Var g e m'
  | c : Fin (g * m') → Var g e m'
  deriving DecidableEq, Fintype

variable (g e m' : ℕ) (A : Type*) [CommRing A]

structure Data where

  G : Fin g → Fin e → MvPolynomial (Option (Fin e)) A

  p : Option (Fin (g * m')) → Fin g → MvPolynomial (Option (Fin e)) A

  s : Option (Fin (g * m')) → Fin g → MvPolynomial (Option (Fin e)) A

  u₀ : Fin g → A

  w₀ : Fin g → Fin e → Fin (m' + 1) → A

  σ₀ : Option (Fin (g * m')) → Fin g → Fin (m' + 1) → A

variable {g e m' A}

abbrev R (g e m' : ℕ) (A : Type*) [CommRing A] := MvPolynomial (Var g e m') A

noncomputable def xser (i : Fin g) : Polynomial (R g e m' A) :=
  Polynomial.C (X (Var.u i)) + Polynomial.X

noncomputable def wser (i : Fin g) (j : Fin e) : Polynomial (R g e m' A) :=
  ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (X (Var.w i j r))

noncomputable def sser (k : Option (Fin (g * m'))) (i : Fin g) : Polynomial (R g e m' A) :=
  ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (X (Var.σ k i r))

noncomputable def coord (i : Fin g) : Option (Fin e) → Polynomial (R g e m' A) :=
  fun o => Option.elim o (xser i) (wser i)

noncomputable def subst (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) : Polynomial (R g e m' A) :=
  MvPolynomial.aeval (coord (m' := m') i) H

noncomputable def cc : Option (Fin (g * m')) → R g e m' A
  | none => 1
  | some k => X (Var.c k)

namespace Data

variable (D : Data g e m' A)

noncomputable def branch (i : Fin g) (j : Fin e) (r : Fin (m' + 1)) : R g e m' A :=
  (subst i (D.G i j)).coeff r

noncomputable def inv (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) : R g e m' A :=
  (sser k i * subst i (D.s k i) - 1).coeff r

noncomputable def tc (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) : R g e m' A :=
  (subst i (D.p k i) * sser k i).coeff r

noncomputable def inc (i : Fin g) (r : Fin (m' + 1)) : R g e m' A :=
  ∑ k : Option (Fin (g * m')), cc k * D.tc k i r

noncomputable def system : Var g e m' → R g e m' A
  | Var.w i j r => D.branch i j r
  | Var.σ k i r => D.inv k i r
  | Var.u i => D.inc i (Fin.last m')
  | Var.c k => D.inc (finProdFinEquiv.symm k).1 (Fin.castSucc (finProdFinEquiv.symm k).2)

def centre : Var g e m' → A
  | Var.u i => D.u₀ i
  | Var.w i j r => D.w₀ i j r
  | Var.σ k i r => D.σ₀ k i r
  | Var.c _ => 0

noncomputable def jacobian (pt : Var g e m' → A) : Matrix (Var g e m') (Var g e m') A :=
  Matrix.of fun v v' => MvPolynomial.eval pt (MvPolynomial.pderiv v' (D.system v))

noncomputable def tcMatrix (pt : Var g e m' → A) : Matrix (Fin (g * m')) (Fin (g * m')) A :=
  Matrix.of fun k k' => MvPolynomial.eval pt
    (D.tc (some k') (finProdFinEquiv.symm k).1 (Fin.castSucc (finProdFinEquiv.symm k).2))

def ptCoord (pt : Var g e m' → A) (i : Fin g) : Option (Fin e) → A :=
  fun o => Option.elim o (pt (Var.u i)) (fun j => pt (Var.w i j 0))

noncomputable def dG (pt : Var g e m' → A) (i : Fin g) (j : Fin e) : A :=
  MvPolynomial.eval (ptCoord pt i) (MvPolynomial.pderiv (some j) (D.G i j))

noncomputable def sVal (pt : Var g e m' → A) (k : Option (Fin (g * m'))) (i : Fin g) : A :=
  MvPolynomial.eval (ptCoord pt i) (D.s k i)

end Data

section Eval

variable (pt : Var g e m' → A)

noncomputable def wpoly (i : Fin g) (j : Fin e) : Polynomial A :=
  ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (pt (Var.w i j r))

noncomputable def spoly (k : Option (Fin (g * m'))) (i : Fin g) : Polynomial A :=
  ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (pt (Var.σ k i r))

noncomputable def coordAt (i : Fin g) : Option (Fin e) → Polynomial A :=
  fun o => Option.elim o (Polynomial.C (pt (Var.u i)) + Polynomial.X) (wpoly pt i)

noncomputable def substAt (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) : Polynomial A :=
  MvPolynomial.aeval (coordAt pt i) H

theorem map_eval_xser (i : Fin g) :
    (xser (e := e) (m' := m') i).map (MvPolynomial.eval pt) = Polynomial.C (pt (Var.u i)) + Polynomial.X := by
  simp [xser]

theorem map_eval_wser (i : Fin g) (j : Fin e) :
    (wser (m' := m') i j).map (MvPolynomial.eval pt) = wpoly pt i j := by
  simp [wser, wpoly, Polynomial.map_sum]

theorem map_eval_sser (k : Option (Fin (g * m'))) (i : Fin g) :
    (sser (e := e) k i).map (MvPolynomial.eval pt) = spoly pt k i := by
  simp [sser, spoly, Polynomial.map_sum]

theorem map_eval_subst (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) :
    (subst (m' := m') i H).map (MvPolynomial.eval pt) = substAt pt i H := by
  change (Polynomial.mapAlgHom (MvPolynomial.aeval pt)) (MvPolynomial.aeval (coord i) H) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  unfold substAt
  congr 2
  funext o
  cases o with
  | none => simp [coord, coordAt, xser]
  | some j => simp [coord, coordAt, wser, wpoly]

variable (D : Data g e m' A)

theorem eval_branch (i : Fin g) (j : Fin e) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.branch i j r) = (substAt pt i (D.G i j)).coeff r := by
  rw [Data.branch, ← Polynomial.coeff_map, map_eval_subst]

theorem eval_inv (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.inv k i r) = (spoly pt k i * substAt pt i (D.s k i) - 1).coeff r := by
  rw [Data.inv, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, map_eval_subst,
    map_eval_sser, Polynomial.map_one]

theorem eval_tc (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.tc k i r) = (substAt pt i (D.p k i) * spoly pt k i).coeff r := by
  rw [Data.tc, ← Polynomial.coeff_map, Polynomial.map_mul, map_eval_subst, map_eval_sser]

theorem eval_inc (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.inc i r) =
      (substAt pt i (D.p none i) * spoly pt none i).coeff r +
        ∑ k : Fin (g * m'), pt (Var.c k) * (substAt pt i (D.p (some k) i) * spoly pt (some k) i).coeff r := by
  rw [Data.inc, map_sum, Fintype.sum_option]
  simp [cc, eval_tc]

end Eval

namespace Data

variable (D : Data g e m' A) {B : Type*} [CommRing B] (f : A →+* B)

noncomputable def map : Data g e m' B where
  G i j := MvPolynomial.map f (D.G i j)
  p k i := MvPolynomial.map f (D.p k i)
  s k i := MvPolynomial.map f (D.s k i)
  u₀ i := f (D.u₀ i)
  w₀ i j r := f (D.w₀ i j r)
  σ₀ k i r := f (D.σ₀ k i r)

theorem map_centre : (D.map f).centre = f ∘ D.centre := by
  funext v; cases v <;> simp [centre, map]

theorem map_xser (i : Fin g) :
    (xser (e := e) (m' := m') (A := A) i).map (MvPolynomial.map f) = xser i := by
  simp [xser]

theorem map_wser (i : Fin g) (j : Fin e) :
    (wser (m' := m') (A := A) i j).map (MvPolynomial.map f) = wser i j := by
  simp [wser, Polynomial.map_sum]

theorem map_sser (k : Option (Fin (g * m'))) (i : Fin g) :
    (sser (e := e) (A := A) k i).map (MvPolynomial.map f) = sser k i := by
  simp [sser, Polynomial.map_sum]

theorem map_subst (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) :
    (subst (m' := m') i H).map (MvPolynomial.map f) = subst i (MvPolynomial.map f H) := by
  unfold subst
  rw [← Polynomial.coe_mapRingHom, ← AlgHom.coe_toRingHom, ← RingHom.comp_apply,
    ← AlgHom.coe_toRingHom, ← RingHom.comp_apply]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro o
    cases o with
    | none => simp [coord, map_xser]
    | some j => simp [coord, map_wser]

theorem map_branch (i : Fin g) (j : Fin e) (r : Fin (m' + 1)) :
    (D.map f).branch i j r = MvPolynomial.map f (D.branch i j r) := by
  rw [branch, branch, ← Polynomial.coeff_map, map_subst]; rfl

theorem map_inv (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    (D.map f).inv k i r = MvPolynomial.map f (D.inv k i r) := by
  rw [inv, inv, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, map_subst, map_sser,
    Polynomial.map_one]; rfl

theorem map_tc (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    (D.map f).tc k i r = MvPolynomial.map f (D.tc k i r) := by
  rw [tc, tc, ← Polynomial.coeff_map, Polynomial.map_mul, map_subst, map_sser]; rfl

theorem map_inc (i : Fin g) (r : Fin (m' + 1)) :
    (D.map f).inc i r = MvPolynomial.map f (D.inc i r) := by
  rw [inc, inc, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_tc]
  cases k <;> simp [cc]

theorem map_system (v : Var g e m') :
    (D.map f).system v = MvPolynomial.map f (D.system v) := by
  cases v <;> simp [system, map_branch, map_inv, map_inc]

theorem _root_.IncidenceSystem.eval_comp_map {ι : Type*} (pt : ι → A) (P : MvPolynomial ι A) :
    MvPolynomial.eval (f ∘ pt) (MvPolynomial.map f P) = f (MvPolynomial.eval pt P) := by
  rw [MvPolynomial.eval_map, show MvPolynomial.eval pt P = MvPolynomial.eval₂ (RingHom.id A) pt P from rfl,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id]

theorem map_jacobian (pt : Var g e m' → A) :
    (D.map f).jacobian (f ∘ pt) = (D.jacobian pt).map f := by
  ext v v'
  simp only [jacobian, Matrix.of_apply, Matrix.map_apply, map_system, MvPolynomial.pderiv_map,
    eval_comp_map]

theorem map_tcMatrix (pt : Var g e m' → A) :
    (D.map f).tcMatrix (f ∘ pt) = (D.tcMatrix pt).map f := by
  ext k k'
  simp only [tcMatrix, Matrix.of_apply, Matrix.map_apply, map_tc, eval_comp_map]

omit f in
theorem map_ptCoord (pt : Var g e m' → A) (i : Fin g) (f : A →+* B) :
    ptCoord (f ∘ pt) i = f ∘ ptCoord pt i := by
  funext o; cases o <;> rfl

theorem map_dG (pt : Var g e m' → A) (i : Fin g) (j : Fin e) :
    (D.map f).dG (f ∘ pt) i j = f (D.dG pt i j) := by
  rw [dG, dG, map_ptCoord, ← eval_comp_map f, ← MvPolynomial.pderiv_map]; rfl

theorem map_sVal (pt : Var g e m' → A) (k : Option (Fin (g * m'))) (i : Fin g) :
    (D.map f).sVal (f ∘ pt) k i = f (D.sVal pt k i) := by
  rw [sVal, sVal, map_ptCoord, ← eval_comp_map f]; rfl

end Data

end IncidenceSystem
