module

public import Mathlib
public import Inductive.IncidenceSystem_Var
public import Structure.IncidenceSystem
public import Abbrev.IncidenceSystem

@[expose] public section

set_option autoImplicit false

open MvPolynomial

namespace IncidenceSystem

variable (g e m' : ℕ) (A : Type*) [CommRing A]


variable {g e m' A}

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

variable (D : Data g e m' A)

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

end Data

end IncidenceSystem

end
