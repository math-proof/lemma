module

public import Mathlib
public import Inductive.IncidenceSystem_Var
public import Structure.IncidenceSystem
public import Abbrev.IncidenceSystem

public section

set_option autoImplicit false

open MvPolynomial

namespace IncidenceSystem

variable (g e m' : ℕ) (A : Type*) [CommRing A]


variable {g e m' A}


public theorem map_eval_xser (i : Fin g) :
    (xser (e := e) (m' := m') i).map (MvPolynomial.eval pt) = Polynomial.C (pt (Var.u i)) + Polynomial.X := by
  simp [xser]


public theorem map_eval_wser (i : Fin g) (j : Fin e) :
    (wser (m' := m') i j).map (MvPolynomial.eval pt) = wpoly pt i j := by
  simp [wser, wpoly, Polynomial.map_sum]


public theorem map_eval_sser (k : Option (Fin (g * m'))) (i : Fin g) :
    (sser (e := e) k i).map (MvPolynomial.eval pt) = spoly pt k i := by
  simp [sser, spoly, Polynomial.map_sum]


public theorem map_eval_subst (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) :
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


public theorem eval_branch (i : Fin g) (j : Fin e) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.branch i j r) = (substAt pt i (D.G i j)).coeff r := by
  rw [Data.branch, ← Polynomial.coeff_map, map_eval_subst]


public theorem eval_inv (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.inv k i r) = (spoly pt k i * substAt pt i (D.s k i) - 1).coeff r := by
  rw [Data.inv, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, map_eval_subst,
    map_eval_sser, Polynomial.map_one]


public theorem eval_tc (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.tc k i r) = (substAt pt i (D.p k i) * spoly pt k i).coeff r := by
  rw [Data.tc, ← Polynomial.coeff_map, Polynomial.map_mul, map_eval_subst, map_eval_sser]


public theorem eval_inc (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.inc i r) =
      (substAt pt i (D.p none i) * spoly pt none i).coeff r +
        ∑ k : Fin (g * m'), pt (Var.c k) * (substAt pt i (D.p (some k) i) * spoly pt (some k) i).coeff r := by
  rw [Data.inc, map_sum, Fintype.sum_option]
  simp [cc, eval_tc]

end Eval

namespace Data

variable (D : Data g e m' A) {B : Type*} [CommRing B] (f : A →+* B)


public theorem map_centre : (D.map f).centre = f ∘ D.centre := by
  funext v; cases v <;> simp [centre, map]


public theorem map_xser (i : Fin g) :
    (xser (e := e) (m' := m') (A := A) i).map (MvPolynomial.map f) = xser i := by
  simp [xser]


public theorem map_wser (i : Fin g) (j : Fin e) :
    (wser (m' := m') (A := A) i j).map (MvPolynomial.map f) = wser i j := by
  simp [wser, Polynomial.map_sum]


public theorem map_sser (k : Option (Fin (g * m'))) (i : Fin g) :
    (sser (e := e) (A := A) k i).map (MvPolynomial.map f) = sser k i := by
  simp [sser, Polynomial.map_sum]


public theorem map_subst (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) :
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


public theorem map_branch (i : Fin g) (j : Fin e) (r : Fin (m' + 1)) :
    (D.map f).branch i j r = MvPolynomial.map f (D.branch i j r) := by
  rw [branch, branch, ← Polynomial.coeff_map, map_subst]; rfl


public theorem map_inv (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    (D.map f).inv k i r = MvPolynomial.map f (D.inv k i r) := by
  rw [inv, inv, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, map_subst, map_sser,
    Polynomial.map_one]; rfl


public theorem map_tc (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    (D.map f).tc k i r = MvPolynomial.map f (D.tc k i r) := by
  rw [tc, tc, ← Polynomial.coeff_map, Polynomial.map_mul, map_subst, map_sser]; rfl


public theorem map_inc (i : Fin g) (r : Fin (m' + 1)) :
    (D.map f).inc i r = MvPolynomial.map f (D.inc i r) := by
  rw [inc, inc, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_tc]
  cases k <;> simp [cc]


public theorem map_system (v : Var g e m') :
    (D.map f).system v = MvPolynomial.map f (D.system v) := by
  cases v <;> simp [system, map_branch, map_inv, map_inc]


public theorem _root_.IncidenceSystem.eval_comp_map {ι : Type*} (pt : ι → A) (P : MvPolynomial ι A) :
    MvPolynomial.eval (f ∘ pt) (MvPolynomial.map f P) = f (MvPolynomial.eval pt P) := by
  rw [MvPolynomial.eval_map, show MvPolynomial.eval pt P = MvPolynomial.eval₂ (RingHom.id A) pt P from rfl,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id]


public theorem map_jacobian (pt : Var g e m' → A) :
    (D.map f).jacobian (f ∘ pt) = (D.jacobian pt).map f := by
  ext v v'
  simp only [jacobian, Matrix.of_apply, Matrix.map_apply, map_system, MvPolynomial.pderiv_map,
    eval_comp_map]


public theorem map_tcMatrix (pt : Var g e m' → A) :
    (D.map f).tcMatrix (f ∘ pt) = (D.tcMatrix pt).map f := by
  ext k k'
  simp only [tcMatrix, Matrix.of_apply, Matrix.map_apply, map_tc, eval_comp_map]

omit f in

public theorem map_ptCoord (pt : Var g e m' → A) (i : Fin g) (f : A →+* B) :
    ptCoord (f ∘ pt) i = f ∘ ptCoord pt i := by
  funext o; cases o <;> rfl


public theorem map_dG (pt : Var g e m' → A) (i : Fin g) (j : Fin e) :
    (D.map f).dG (f ∘ pt) i j = f (D.dG pt i j) := by
  rw [dG, dG, map_ptCoord, ← eval_comp_map f, ← MvPolynomial.pderiv_map]; rfl


public theorem map_sVal (pt : Var g e m' → A) (k : Option (Fin (g * m'))) (i : Fin g) :
    (D.map f).sVal (f ∘ pt) k i = f (D.sVal pt k i) := by
  rw [sVal, sVal, map_ptCoord, ← eval_comp_map f]; rfl

end Data

end IncidenceSystem
