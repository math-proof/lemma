/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.AffineVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Opposites

open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]

section Evaluation

/-- Evaluation of an element of the $\bar k$-coordinate ring $\bar k[X]$ at a point $P \in X$.
Given a class $[f] \in \bar k[X] = \bar k[X_1, \dots, X_n]/I(X)$ and a point $P \in X$, this
yields $f(P) \in \bar k$. Well-defined because $I(X)$ vanishes on $X$. -/
noncomputable def evalBarAtPoint {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X) :
    AffineCoordinateRingBar X →+* AlgebraicClosure k :=
  Ideal.Quotient.lift (idealOfAlgebraicSet X) (eval P) (fun _f hf => hf P hP)

/-- Compatibility of `evalBarAtPoint` with the quotient map: evaluating the class of a
polynomial $f$ at $P$ equals the ordinary polynomial evaluation $f(P)$. -/
@[simp]
theorem evalBarAtPoint_mk {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (f : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    evalBarAtPoint k X P hP (Ideal.Quotient.mk _ f) = eval P f :=
  Ideal.Quotient.lift_mk _ _ _

end Evaluation

section RegularFunctions

variable {k}
variable {n : ℕ} {X : Set (Fin n → AlgebraicClosure k)}
variable [hdom : IsDomain (AffineCoordinateRingBar X)]

/-- Definition 15.2 (regularity at a point). A rational function
$r \in \bar k(X) = \mathrm{Frac}(\bar k[X])$ is *regular at* $P \in X$ if it can be
written as a fraction $r = f/g$ with $f, g \in \bar k[X]$ and $g(P) \neq 0$.
Equivalently: there exists $g \in \bar k[X]$ with $g(P) \neq 0$ such that $g \cdot r$
lies in the image of $\bar k[X]$ in the fraction field. -/
def IsRegularAt
    (r : FractionRing (AffineCoordinateRingBar X))
    (P : Fin n → AlgebraicClosure k)
    (hP : P ∈ X) : Prop :=
  ∃ g : AffineCoordinateRingBar X,
    evalBarAtPoint k X P hP g ≠ 0 ∧
    algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) g * r ∈
      Set.range (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)))

/-- The *denominator ideal* of a rational function $r \in \bar k(X)$: the ideal of
elements $g \in \bar k[X]$ such that $g \cdot r$ lies in $\bar k[X]$. Its non-vanishing
locus is the regular locus of $r$. -/
noncomputable def denominatorIdeal
    (r : FractionRing (AffineCoordinateRingBar X)) :
    Ideal (AffineCoordinateRingBar X) where
  carrier := {g : AffineCoordinateRingBar X |
    algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) g * r ∈
      Set.range (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)))}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, zero_mul]
    exact ⟨0, map_zero _⟩
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add, add_mul] at ha hb ⊢
    obtain ⟨fa, hfa⟩ := ha
    obtain ⟨fb, hfb⟩ := hb
    exact ⟨fa + fb, by rw [map_add, hfa, hfb]⟩
  smul_mem' := by
    intro c g hg
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hg ⊢
    rw [mul_assoc]
    obtain ⟨fg, hfg⟩ := hg
    exact ⟨c * fg, by rw [map_mul, hfg]⟩


/-- The *regular domain* (or *regular locus*) of $r \in \bar k(X)$: the set of points
$P \in X$ at which $r$ is regular. -/
def regularDomain
    (r : FractionRing (AffineCoordinateRingBar X)) :
    Set (Fin n → AlgebraicClosure k) :=
  {P : Fin n → AlgebraicClosure k | ∃ (hP : P ∈ X), IsRegularAt r P hP}

/-- Evaluation of a rational function $r \in \bar k(X)$ at a point $P$ where $r$ is
regular: choose a representation $r = f/g$ with $g(P) \neq 0$ and return
$f(P)/g(P) \in \bar k$. The value is independent of the choice of representation
(though that is not proven here). -/
noncomputable def evalRatFunAt
    (r : FractionRing (AffineCoordinateRingBar X))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsRegularAt r P hP) : AlgebraicClosure k :=
  let g := hreg.choose
  let hg := hreg.choose_spec
  let f := hg.2.choose
  evalBarAtPoint k X P hP f / evalBarAtPoint k X P hP g

/-- A tuple $(\varphi_1, \dots, \varphi_{n_\mathrm{cod}})$ of rational functions in
$\bar k(X)$ is *regular at $P \in X$* if each component $\varphi_i$ is regular at $P$. -/
def IsTupleRegularAt
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X))
    (P : Fin m → AlgebraicClosure k)
    (hP : P ∈ X) : Prop :=
  ∀ i : Fin n_cod, IsRegularAt (φ i) P hP

/-- Componentwise evaluation of a tuple of rational functions at a point of common
regularity: produces a point of $\bar k^{n_\mathrm{cod}}$. -/
noncomputable def evalTupleAt
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X))
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt φ P hP) :
    Fin n_cod → AlgebraicClosure k :=
  fun j => evalRatFunAt (φ j) P hP (hreg j)

/-- Definition 15.4 (affine rational map). A *rational map* $\varphi : X \dashrightarrow Y$
between affine algebraic sets is a tuple of components $(\varphi_1, \dots, \varphi_{n_\mathrm{cod}})$
with each $\varphi_i \in \bar k(X)$, together with the requirement that whenever the tuple
is regular at $P \in X$, the resulting point $(\varphi_1(P), \dots, \varphi_{n_\mathrm{cod}}(P))$
lies in the target $Y$. -/
structure AffineRationalMap
    (X : Set (Fin m → AlgebraicClosure k))
    (Y : Set (Fin n_cod → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)] where
  components : Fin n_cod → FractionRing (AffineCoordinateRingBar X)
  image_mem : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt components P hP),
    evalTupleAt components P hP hreg ∈ Y

/-- The *domain of definition* of a rational map (as a tuple of rational functions):
the set of points of $X$ where every component is regular. -/
def rationalMapDomain
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) :
    Set (Fin m → AlgebraicClosure k) :=
  {P : Fin m → AlgebraicClosure k | ∃ (hP : P ∈ X), IsTupleRegularAt φ P hP}


/-- A rational map $\varphi$ is *regular* (a morphism of affine varieties) if it is
regular at every point of $X$. -/
def IsRegularRationalMap
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) : Prop :=
  ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X), IsTupleRegularAt φ P hP


end RationalMaps

section DominantAndBirational

variable {k : Type*} [Field k]

open MvPolynomial

/-- The *Zariski closure* of a subset $S \subseteq \bar k^n$: the smallest algebraic
set containing $S$, namely $\mathcal{V}(\mathcal{I}(S))$. -/
def zariskiClosure {n : ℕ}
    (S : Set (Fin n → AlgebraicClosure k)) :
    Set (Fin n → AlgebraicClosure k) :=
  AlgebraicSet k n ((idealOfAlgebraicSet S : Ideal _) : Set _)


/-- The set-theoretic image of a rational map (defined on its domain): the set of all
$Q \in \bar k^{n_\mathrm{cod}}$ that arise as the value of $\varphi$ at some point of
$\mathrm{dom}(\varphi)$. -/
def rationalMapImage {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) :
    Set (Fin n_cod → AlgebraicClosure k) :=
  {Q : Fin n_cod → AlgebraicClosure k |
    ∃ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
      (hreg : IsTupleRegularAt φ P hP),
      evalTupleAt φ P hP hreg = Q}

/-- Definition 15.7 (dominant rational map). A rational map $\varphi : X \dashrightarrow Y$
is *dominant* if its image is Zariski-dense in $Y$, i.e. the Zariski closure of the image
equals $Y$. -/
def IsDominantRationalMap {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (Y : Set (Fin n_cod → AlgebraicClosure k))
    (φ : AffineRationalMap X Y) : Prop :=
  zariskiClosure (rationalMapImage φ.components) = Y

/-- The *composition domain* of $\psi \circ \varphi$ where $\varphi : X \dashrightarrow Y$
and $\psi : Y \dashrightarrow X$: the set of points $P \in X$ where $\varphi$ is regular
at $P$, $\varphi(P) \in Y$, and $\psi$ is regular at $\varphi(P)$. -/
def compositionDomain {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (ψ : AffineRationalMap Y X) :
    Set (Fin m → AlgebraicClosure k) :=
  {P : Fin m → AlgebraicClosure k |
    ∃ (hP : P ∈ X) (hregφ : IsTupleRegularAt φ.components P hP),
      ∃ (hQ : evalTupleAt φ.components P hP hregφ ∈ Y),
        IsTupleRegularAt ψ.components
          (evalTupleAt φ.components P hP hregφ) hQ}

/-- Pointwise evaluation of the composition $\psi \circ \varphi$ at $P \in
\mathrm{compositionDomain}(\varphi, \psi)$: returns $\psi(\varphi(P)) \in \bar k^m$. -/
noncomputable def evalCompositionAt {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (ψ : AffineRationalMap Y X)
    (P : Fin m → AlgebraicClosure k)
    (hcomp : P ∈ compositionDomain φ ψ) :
    Fin m → AlgebraicClosure k :=
  let hP := hcomp.choose
  let hregφ := hcomp.choose_spec.choose
  let hQ := hcomp.choose_spec.choose_spec.choose
  let hregψ := hcomp.choose_spec.choose_spec.choose_spec
  evalTupleAt ψ.components
    (evalTupleAt φ.components P hP hregφ) hQ hregψ

/-- Definition 15.10 (birational equivalence). Two affine algebraic sets $X$ and $Y$
are *birationally equivalent* if there exist dominant rational maps
$\varphi : X \dashrightarrow Y$ and $\psi : Y \dashrightarrow X$ whose compositions (on
their composition domains) agree with the respective identities. -/
def AreBirationallyEquivalent {m n_cod : ℕ}
    (X : Set (Fin m → AlgebraicClosure k))
    (Y : Set (Fin n_cod → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)] : Prop :=
  ∃ (φ : AffineRationalMap X Y) (ψ : AffineRationalMap Y X),
    IsDominantRationalMap Y φ ∧
    IsDominantRationalMap X ψ ∧
    (∀ (P : Fin m → AlgebraicClosure k)
       (hcomp : P ∈ compositionDomain φ ψ),
       evalCompositionAt φ ψ P hcomp = P) ∧
    (∀ (Q : Fin n_cod → AlgebraicClosure k)
       (hcomp : Q ∈ compositionDomain ψ φ),
       evalCompositionAt ψ φ Q hcomp = Q)

end DominantAndBirational

section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

/-- A ring homomorphism $\theta : \bar k(Y) \to \bar k(X)$ is a *$\bar k$-algebra
homomorphism of function fields* if it fixes the scalars from $\bar k$ (under the
canonical inclusions $\bar k \hookrightarrow \bar k[Y] \hookrightarrow \bar k(Y)$). -/
def IsKbarFunctionFieldHom {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X)) : Prop :=
  ∀ r : AlgebraicClosure k,
    θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r))) =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r))

/-- The substitution homomorphism $\bar k[Y_1, \dots, Y_{n_\mathrm{cod}}] \to \bar k(X)$
sending each coordinate $Y_i$ to the corresponding component $\varphi_i \in \bar k(X)$.
This is the first step in building the pullback induced by a rational map. -/
noncomputable def dominantPullbackSubstHom
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) :
    MvPolynomial (Fin n_cod) (AlgebraicClosure k) →+*
    FractionRing (AffineCoordinateRingBar X) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
      ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C))
    φ

/-- Key technical lemma: the substitution homomorphism associated to a rational map
$\varphi : X \dashrightarrow Y$ kills the ideal $\mathcal{I}(Y)$. Combines the
Nullstellensatz with the property that the values of $\varphi$ land in $Y$. This is what
allows the substitution map to descend to $\bar k[Y] \to \bar k(X)$. -/
theorem dominantPullbackSubstHom_kills_ideal
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k))
    (hf : f ∈ idealOfAlgebraicSet Y) :
    dominantPullbackSubstHom φ.components f = 0 := by


  by_contra hr

  obtain ⟨⟨a_r, ⟨b_r, hb_r⟩⟩, hab_r⟩ := IsLocalization.surj
    (nonZeroDivisors (AffineCoordinateRingBar X))
    (dominantPullbackSubstHom φ.components f)
  simp only at hab_r

  have ha_ne : a_r ≠ 0 := by
    intro ha0; apply hr
    have h1 : dominantPullbackSubstHom φ.components f *
        (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) b_r = 0 := by
      rw [hab_r, ha0, map_zero]
    have hb_ne_frac : (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) b_r ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      exact mem_nonZeroDivisors_iff_ne_zero.mp hb_r
    exact (mul_eq_zero.mp h1).resolve_right hb_ne_frac
  have hb_ne : b_r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_r

  choose cd_j hcd_j using
    (fun j => IsLocalization.surj (nonZeroDivisors (AffineCoordinateRingBar X)) (φ.components j))

  set product := a_r * (b_r * ∏ j : Fin n_cod, ((cd_j j).2 : AffineCoordinateRingBar X))
    with hprod_def

  have hprod_ne : product ≠ 0 := by
    apply mul_ne_zero ha_ne (mul_ne_zero hb_ne _)
    exact Finset.prod_ne_zero_iff.mpr (fun j _ =>
      mem_nonZeroDivisors_iff_ne_zero.mp (cd_j j).2.property)


  have h_clearing : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
      (hreg_comp : IsTupleRegularAt φ.components P hP)
      (p : MvPolynomial (Fin n_cod) (AlgebraicClosure k)),
      ∃ (g₀ : AffineCoordinateRingBar X) (f₀ : AffineCoordinateRingBar X),
        evalBarAtPoint k X P hP g₀ ≠ 0 ∧
        (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))) f₀ =
        (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))) g₀ *
          (dominantPullbackSubstHom φ.components) p ∧
        MvPolynomial.eval (evalTupleAt φ.components P hP hreg_comp) p *
          evalBarAtPoint k X P hP g₀ = evalBarAtPoint k X P hP f₀ := by
    intro P hP hreg_comp p
    induction p using MvPolynomial.induction_on with
    | C c =>
      refine ⟨1, Ideal.Quotient.mk _ (MvPolynomial.C c), ?_, ?_, ?_⟩
      · simp [map_one]
      · simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
          map_one, one_mul]
        rfl
      · simp only [MvPolynomial.eval_C, map_one, mul_one, evalBarAtPoint_mk]
    | add p q ihp ihq =>
      obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
      obtain ⟨gq, fq, hgq_ne, hfq_eq, hfq_eval⟩ := ihq
      refine ⟨gp * gq, gq * fp + gp * fq, ?_, ?_, ?_⟩
      · rw [map_mul]; exact mul_ne_zero hgp_ne hgq_ne
      · simp only [map_mul, map_add]
        rw [mul_add]
        congr 1
        · rw [hfp_eq]; ring
        · rw [hfq_eq]; ring
      · simp only [map_mul, map_add]
        linear_combination (evalBarAtPoint k X P hP gq) * hfp_eval +
          (evalBarAtPoint k X P hP gp) * hfq_eval
    | mul_X p j ihp =>
      obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
      obtain ⟨gj, hgj_ne, hgj_mem⟩ := hreg_comp j
      obtain ⟨aj, haj_eq⟩ := hgj_mem
      refine ⟨gp * gj, fp * aj, ?_, ?_, ?_⟩
      · rw [map_mul]; exact mul_ne_zero hgp_ne hgj_ne
      · simp only [map_mul]
        rw [show (dominantPullbackSubstHom φ.components) (MvPolynomial.X j) =
          φ.components j by
          simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_X']]
        rw [hfp_eq, haj_eq]
        ring
      · simp only [MvPolynomial.eval_X, map_mul]
        have hσj : evalTupleAt φ.components P hP hreg_comp j *
            evalBarAtPoint k X P hP gj = evalBarAtPoint k X P hP aj := by
          set g₀ := (hreg_comp j).choose with hg₀_def
          set f₀ := (hreg_comp j).choose_spec.2.choose with hf₀_def
          have hg₀_ne : evalBarAtPoint k X P hP g₀ ≠ 0 := (hreg_comp j).choose_spec.1
          have hf₀_eq : (algebraMap (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))) f₀ =
            (algebraMap (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))) g₀ * φ.components j :=
            (hreg_comp j).choose_spec.2.choose_spec
          have h_cross : f₀ * gj = aj * g₀ := by
            apply IsFractionRing.injective (AffineCoordinateRingBar X)
              (FractionRing (AffineCoordinateRingBar X))
            simp only [map_mul]
            rw [hf₀_eq, haj_eq]
            ring
          show evalRatFunAt (φ.components j) P hP (hreg_comp j) *
            evalBarAtPoint k X P hP gj = evalBarAtPoint k X P hP aj
          simp only [evalRatFunAt]
          rw [div_mul_eq_mul_div, div_eq_iff hg₀_ne]
          rw [← map_mul, ← map_mul, h_cross]
        calc (MvPolynomial.eval _ p) *
              (evalTupleAt φ.components P hP hreg_comp j) *
              ((evalBarAtPoint k X P hP gp) * (evalBarAtPoint k X P hP gj))
            = ((MvPolynomial.eval _ p) * (evalBarAtPoint k X P hP gp)) *
              ((evalTupleAt φ.components P hP hreg_comp j) *
               (evalBarAtPoint k X P hP gj)) := by ring
          _ = (evalBarAtPoint k X P hP fp) * (evalBarAtPoint k X P hP aj) := by
              rw [hfp_eval, hσj]

  have hprod_vanishes : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X),
      evalBarAtPoint k X P hP product = 0 := by
    intro P hP
    simp only [hprod_def, map_mul, map_prod]
    by_cases hbP : evalBarAtPoint k X P hP b_r = 0
    · simp [hbP]
    by_cases hdP : ∃ j, evalBarAtPoint k X P hP ((cd_j j).2 : AffineCoordinateRingBar X) = 0
    · obtain ⟨j, hjP⟩ := hdP
      have : (∏ i : Fin n_cod,
          evalBarAtPoint k X P hP ((cd_j i).2 : AffineCoordinateRingBar X)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) hjP
      simp [this]
    push Not at hdP

    have hreg_comp : IsTupleRegularAt φ.components P hP := by
      intro j
      exact ⟨((cd_j j).2 : AffineCoordinateRingBar X), hdP j,
        ⟨(cd_j j).1, ((hcd_j j).symm.trans (mul_comm _ _))⟩⟩

    have hf_vanish : MvPolynomial.eval (evalTupleAt φ.components P hP hreg_comp) f = 0 :=
      hf _ (φ.image_mem P hP hreg_comp)

    obtain ⟨g₀, f₀, hg₀_ne, hf₀_eq, hf₀_eval⟩ := h_clearing P hP hreg_comp f

    rw [hf_vanish, zero_mul] at hf₀_eval


    have h_cross : f₀ * b_r = g₀ * a_r := by
      apply IsFractionRing.injective (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))
      simp only [map_mul]
      calc _ = (algebraMap _ _ g₀ * dominantPullbackSubstHom φ.components f) *
                algebraMap _ _ b_r := by rw [hf₀_eq]
        _ = algebraMap _ _ g₀ * (dominantPullbackSubstHom φ.components f *
                algebraMap _ _ b_r) := by ring
        _ = algebraMap _ _ g₀ * algebraMap _ _ a_r := by rw [hab_r]
    have h_eval_cross : evalBarAtPoint k X P hP f₀ * evalBarAtPoint k X P hP b_r =
        evalBarAtPoint k X P hP g₀ * evalBarAtPoint k X P hP a_r := by
      rw [← map_mul, ← map_mul, h_cross]

    rw [hf₀_eval.symm, zero_mul] at h_eval_cross
    have haP : evalBarAtPoint k X P hP a_r = 0 := by
      rcases mul_eq_zero.mp h_eval_cross.symm with hg₀P | haP
      · exact absurd hg₀P hg₀_ne
      · exact haP
    simp [haP]

  have hprod_zero : product = 0 := by
    obtain ⟨f_poly, hf_poly⟩ := Ideal.Quotient.mk_surjective product
    suffices h_mem : f_poly ∈ idealOfAlgebraicSet X by
      rw [← hf_poly]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h_mem
    rw [mem_idealOfAlgebraicSet_iff]
    intro P hP
    have := hprod_vanishes P hP
    rw [← hf_poly, evalBarAtPoint_mk] at this
    exact this
  exact hprod_ne hprod_zero

/-- Descent of the substitution homomorphism to a ring map $\bar k[Y] \to \bar k(X)$:
since the substitution kills $\mathcal{I}(Y)$, it factors through the quotient
$\bar k[Y_1,\dots,Y_{n_\mathrm{cod}}]/\mathcal{I}(Y) = \bar k[Y]$. -/
noncomputable def dominantPullbackToFractionRing
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y) :
    AffineCoordinateRingBar Y →+* FractionRing (AffineCoordinateRingBar X) :=
  Ideal.Quotient.lift (idealOfAlgebraicSet Y)
    (dominantPullbackSubstHom φ.components)
    (dominantPullbackSubstHom_kills_ideal φ)

/-- Each coordinate $\varphi_i = \varphi^*(Y_i)$ lies in $\bar k[X] \subseteq \bar k(X)$,
viewed via the substitution homomorphism. (This is the form needed for the pullback to
descend to coordinate rings; the proof uses regularity of the rational map.) -/
class of a constant polynomial $C(r)$ in $\bar k[Y]$ to the class of $C(r)$ in $\bar k[X]$.
This is the coordinate-ring version of `IsKbarFunctionFieldHom` for $\varphi^*$. -/
noncomputable def functionFieldMorphismComponents {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X)) :
    Fin n_cod → FractionRing (AffineCoordinateRingBar X) :=
  fun j => θ (algebraMap (AffineCoordinateRingBar Y)
    (FractionRing (AffineCoordinateRingBar Y))
    (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j)))

/-- Independence of representation for `evalRatFunAt`: any representation $r = f/g$ with
$g(P) \neq 0$ gives the same value $f(P)/g(P)$ for the evaluation of $r$ at $P$. -/
lemma evalRatFunAt_eq {k : Type*} [Field k] {n : ℕ}
    {X : Set (Fin n → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (r : FractionRing (AffineCoordinateRingBar X))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsRegularAt r P hP)
    (g f_val : AffineCoordinateRingBar X)
    (hg_ne : evalBarAtPoint k X P hP g ≠ 0)
    (hgr : algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) g * r =
      algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)) f_val) :
    evalRatFunAt r P hP hreg = evalBarAtPoint k X P hP f_val /
      evalBarAtPoint k X P hP g := by
  show evalBarAtPoint k X P hP hreg.choose_spec.2.choose /
    evalBarAtPoint k X P hP hreg.choose =
    evalBarAtPoint k X P hP f_val / evalBarAtPoint k X P hP g
  set g₀ := hreg.choose with hg₀_def
  set f₀ := hreg.choose_spec.2.choose with hf₀_def
  have hg₀_ne : evalBarAtPoint k X P hP g₀ ≠ 0 := hreg.choose_spec.1
  have hf₀_eq : (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) f₀ =
    (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) g₀ * r :=
    hreg.choose_spec.2.choose_spec
  have h_cross : f₀ * g = g₀ * f_val := by
    apply IsFractionRing.injective (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))
    simp only [map_mul]
    calc _ = (algebraMap _ _ g₀ * r) * algebraMap _ _ g := by rw [hf₀_eq]
      _ = algebraMap _ _ g₀ * (algebraMap _ _ g * r) := by ring
      _ = algebraMap _ _ g₀ * algebraMap _ _ f_val := by rw [hgr]
  have h_eval_cross : evalBarAtPoint k X P hP f₀ * evalBarAtPoint k X P hP g =
      evalBarAtPoint k X P hP g₀ * evalBarAtPoint k X P hP f_val := by
    rw [← map_mul, ← map_mul, h_cross]
  rw [div_eq_div_iff hg₀_ne hg_ne]
  rw [mul_comm (evalBarAtPoint k X P hP f_val)]
  exact h_eval_cross

/-- Characterizing property of the induced rational map: evaluating a polynomial $f$
in the target coordinates at the image point $\theta(P)$ equals the value of $\theta(f)$
at the point $P$. This is the key step proving compatibility of $\theta$ with point
evaluation. -/
theorem characterizing_property
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k))
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP)
    (hreg_θf : IsRegularAt
      (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
      P hP) :
    MvPolynomial.eval (evalTupleAt (functionFieldMorphismComponents θ) P hP hreg) f =
    evalRatFunAt
      (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
      P hP hreg_θf := by

  obtain ⟨g₀, f₀, hg₀_ne, hf₀_eq, hf₀_eval⟩ :=
    eval₂_clearing_denominators θ hθ P hP hreg f


  have h_eval₂ := theta_algebraMap_mk_eq_eval₂ θ hθ f


  have hgr : (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) g₀ *
    θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) f₀ := by
    rw [h_eval₂]; exact hf₀_eq.symm

  rw [evalRatFunAt_eq _ P hP hreg_θf g₀ f₀ hg₀_ne hgr]

  rw [eq_div_iff hg₀_ne]

  exact hf₀_eval

/-- Any ring homomorphism $\theta : \bar k(Y) \to \bar k(X)$ kills the ideal $\mathcal{I}(Y)$:
the polynomial $f \in \mathcal{I}(Y)$ becomes zero in $\bar k[Y]$ (since the quotient is
the coordinate ring), so its image in $\bar k(Y)$ is zero, hence $\theta(f) = 0$. -/
lemma θ_kills_ideal {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k))
    (hf : f ∈ idealOfAlgebraicSet Y) :
    θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) = 0 := by
  have hmk : (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f : AffineCoordinateRingBar Y) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have : (Ideal.Quotient.mk (idealOfAlgebraicSet Y)) f = (0 : AffineCoordinateRingBar Y) :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hf
  rw [this, map_zero, map_zero]

/-- The zero rational function is regular at every point: with denominator $g = 1$ (which
satisfies $g(P) = 1 \neq 0$), we have $g \cdot 0 = 0$ in the image of $\bar k[X]$. -/
lemma isRegularAt_zero {m : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X) :
    IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP := by
  refine ⟨1, ?_, ?_⟩
  · simp [evalBarAtPoint, ne_eq, one_ne_zero, not_false_eq_true]
  · simp only [map_one, one_mul]
    exact ⟨0, by simp⟩

/-- The value of the zero rational function at any point is zero. -/
lemma evalRatFunAt_zero {m : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP) :
    evalRatFunAt 0 P hP hreg = 0 := by


  unfold evalRatFunAt
  have hmem := hreg.choose_spec.2
  have h_eq : (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) hmem.choose =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) hreg.choose * 0 := hmem.choose_spec
  have h_zero : hmem.choose = 0 := by
    have : (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) hmem.choose = 0 := by
      rw [h_eq]; ring
    rwa [map_eq_zero_iff _ (IsFractionRing.injective _ _)] at this
  simp [evalBarAtPoint]

/-- The image of the rational map induced by a $\bar k$-algebra homomorphism $\theta$
lands in $Y$: at any point $P$ where the components are regular, the evaluated tuple
$(\theta(Y_1)(P), \dots, \theta(Y_{n_\mathrm{cod}})(P))$ satisfies every equation of
$\mathcal{I}(Y)$, hence lies in $Y$. -/
theorem functionFieldMorphism_image_mem {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (hY : IsAlgebraicSubset k n_cod Y)
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP) :
    evalTupleAt (functionFieldMorphismComponents θ) P hP hreg ∈ Y := by


  suffices h : evalTupleAt (functionFieldMorphismComponents θ) P hP hreg ∈
      AlgebraicSet k n_cod ((idealOfAlgebraicSet Y) : Set _) by
    rwa [algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hY] at h
  intro f hf


  have hθf_zero := θ_kills_ideal θ f hf
  have hreg_0 : IsRegularAt
      (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
      P hP := by
    rw [hθf_zero]; exact isRegularAt_zero P hP
  rw [characterizing_property θ hθ f P hP hreg hreg_0]


  have hreg_0' : IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP :=
    hθf_zero ▸ hreg_0
  have : evalRatFunAt (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f))) P hP hreg_0 =
    evalRatFunAt 0 P hP hreg_0' := by
    congr 1
  rw [this]
  exact evalRatFunAt_zero P hP hreg_0'

/-- The *rational map induced* by a $\bar k$-algebra homomorphism $\theta : \bar k(Y) \to
\bar k(X)$: its components are $\theta(Y_1), \dots, \theta(Y_{n_\mathrm{cod}})$, and the
image-membership condition is provided by `functionFieldMorphism_image_mem`. This is the
construction of Theorem 15.8(iii) producing $\varphi$ from $\theta$. -/
noncomputable def functionFieldMorphismInducedMap {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (hY : IsAlgebraicSubset k n_cod Y) :
    AffineRationalMap X Y where
  components := functionFieldMorphismComponents θ
  image_mem := functionFieldMorphism_image_mem θ hθ hY

/-- The natural ring homomorphism $k[X] \to \bar k[X]$ extending scalars from the base
field $k$ to its algebraic closure $\bar k$: descends the map induced on polynomials by
$k \hookrightarrow \bar k$ to the quotient defining $k[X]$. -/
noncomputable def coordRingToBar {n : ℕ}
    (X : Set (Fin n → AlgebraicClosure k)) :
    AffineCoordinateRing X →+* AffineCoordinateRingBar X :=
  Ideal.Quotient.lift (idealOverK X)
    ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp
      (MvPolynomial.map (algebraMap k (AlgebraicClosure k))))
    (fun f hf => by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_idealOverK_iff.mp hf))

/-- The composite $k[X] \to \bar k[X] \hookrightarrow \bar k(X)$ is injective. Needed to
extend the scalar-extension map to the level of function fields. -/
theorem coordRingToBar_comp_algebraMap_injective
    {k : Type*} [Field k]
    {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRing X)] :
    Function.Injective
      ((algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))).comp
        (coordRingToBar X)) :=
  (IsFractionRing.injective (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))).comp (fun a b hab => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hab' : Ideal.Quotient.mk (idealOfAlgebraicSet X)
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) a) =
      Ideal.Quotient.mk (idealOfAlgebraicSet X)
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) b) := by
      change coordRingToBar X (Ideal.Quotient.mk (idealOverK X) a) =
        coordRingToBar X (Ideal.Quotient.mk (idealOverK X) b) at hab
      simp only [coordRingToBar] at hab
      exact hab
    rw [Ideal.Quotient.eq] at hab'
    have hmem : a - b ∈ idealOverK X :=
      mem_idealOverK_iff.mpr (by rwa [map_sub])
    exact Ideal.Quotient.eq.mpr hmem)

/-- Scalar extension on function fields: the natural homomorphism $k(X) \to \bar k(X)$
obtained by extending the coordinate-ring map $k[X] \to \bar k[X]$ to fraction fields. -/
noncomputable def functionFieldToBar {n : ℕ}
    (X : Set (Fin n → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRing X)] :
    FractionRing (AffineCoordinateRing X) →+*
    FractionRing (AffineCoordinateRingBar X) :=
  IsFractionRing.lift
    (g := (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
      (coordRingToBar X))
    (coordRingToBar_comp_algebraMap_injective X)

/-- A rational map $\varphi : X \dashrightarrow Y$ is *defined over $k$* if each of its
components lies in the image of $k(X) \to \bar k(X)$, i.e. can be represented by a tuple
of rational functions with coefficients in the base field $k$. -/
def AffineRationalMap.IsDefinedOverK {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRing X)]
    (φ : AffineRationalMap X Y) : Prop :=
  ∀ j : Fin n_cod, φ.components j ∈
    Set.range (functionFieldToBar X)

/-- The coordinate-ring pullback over $k$: for a dominant rational map defined over $k$
between $k$-defined varieties, the pullback descends to a ring map $k[Y] \to k[X]$ on
the $k$-coordinate rings. -/
end Corollary1512

section Corollary159

variable (k : Type*) [Field k]

open MvPolynomial CategoryTheory

/-- The $\bar k$-algebra structure on $\bar k[Z]$ obtained from the natural map
$\bar k \hookrightarrow \bar k[x_1, \dots, x_n]$ followed by the quotient. -/
noncomputable instance instAlgebraAffineCoordinateRingBar {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :
    Algebra (AlgebraicClosure k) (AffineCoordinateRingBar Z) :=
  show Algebra (AlgebraicClosure k)
    (MvPolynomial (Fin n) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet Z) from
    Ideal.Quotient.algebra (AlgebraicClosure k)

/-- Bundled object of the category of affine varieties (over $\bar k$) with domain
coordinate ring: packages a dimension, a carrier set, the algebraic-subset condition,
and the integral-domain property of $\bar k[X]$. -/
structure AffineVarietyDom where
  dim : ℕ
  carrier : Set (Fin dim → AlgebraicClosure k)
  isAlgebraic : IsAlgebraicSubset k dim carrier
  isDomain : IsDomain (AffineCoordinateRingBar carrier)

attribute [instance] AffineVarietyDom.isDomain

/-- A morphism in `AffineVarietyDom k`: a dominant rational map between the underlying
varieties, bundling a rational map and a proof that it is dominant. -/
@[ext]
structure AffineVarietyDom.Hom (V W : AffineVarietyDom k) where
  map : @AffineRationalMap k _ V.dim W.dim V.carrier W.carrier V.isDomain
  dominant : @IsDominantRationalMap k _ V.dim W.dim V.carrier
    V.isDomain W.carrier map

/-- The identity rational map on $V$: defined as the rational map induced by the
identity ring homomorphism on $\bar k(V)$, which is a $\bar k$-algebra homomorphism. -/
noncomputable def AffineVarietyDom.idMap
    {k : Type*} [Field k]
    (V : AffineVarietyDom k) :
    @AffineRationalMap k _ V.dim V.dim V.carrier V.carrier V.isDomain :=
  @functionFieldMorphismInducedMap k _ V.dim V.dim V.carrier V.carrier V.isDomain V.isDomain
    (RingHom.id _) (fun _ => rfl) V.isAlgebraic

/-- The function-field pullback $\varphi^*$ is a morphism over $\bar k$: it fixes the
images of all constants $c \in \bar k$. (Primed variant used internally.) -/
structure FunctionFieldObj where
  carrier : Type*
  [fieldInst : Field carrier]
  [algInst : Algebra (AlgebraicClosure k) carrier]
  finitelyGenerated : Algebra.FiniteType (AlgebraicClosure k) carrier

attribute [instance] FunctionFieldObj.fieldInst FunctionFieldObj.algInst

/-- Coerce a `FunctionFieldObj` to its underlying field. -/
instance : CoeSort (FunctionFieldObj k) (Type*) := ⟨FunctionFieldObj.carrier⟩

/-- A morphism $F \to G$ in the category of function fields is a $\bar k$-algebra
homomorphism $G \to F$ on the underlying fields (note the direction: the category is
contravariant relative to the algebra-homomorphism direction). -/
@[ext]
structure FunctionFieldObj.Hom (F G : FunctionFieldObj k) where
  toAlgHom : G.carrier →ₐ[AlgebraicClosure k] F.carrier

/-- Category structure on `FunctionFieldObj k`: objects are finitely generated function
fields over $\bar k$ and morphisms are $\bar k$-algebra homomorphisms in the reversed
direction (so the resulting equivalence with `AffineVarietyDom` is covariant in this
formalisation). -/
noncomputable instance : Category (FunctionFieldObj k) where
  Hom F G := FunctionFieldObj.Hom k F G
  id F := ⟨AlgHom.id (AlgebraicClosure k) F.carrier⟩
  comp f g := ⟨f.toAlgHom.comp g.toAlgHom⟩

/-- If $\varphi : X \dashrightarrow Y$ and $\psi : Y \dashrightarrow X$ are dominant
rational maps whose composition $\psi \circ \varphi$ is the identity on its domain in
$X$, then the composition of their function-field pullbacks is the identity on $\bar k(X)$. -/
noncomputable def functionFieldIsoToAlgEquiv
    (F G : FunctionFieldObj k)
    (i : F ≅ G) :
    G.carrier ≃ₐ[AlgebraicClosure k] F.carrier :=
  AlgEquiv.ofAlgHom
    i.hom.toAlgHom
    i.inv.toAlgHom
    (by
      have h := i.hom_inv_id
      exact congr_arg FunctionFieldObj.Hom.toAlgHom h)
    (by
      have h := i.inv_hom_id
      exact congr_arg FunctionFieldObj.Hom.toAlgHom h)

/-- Inverse of `functionFieldIsoToAlgEquiv`: convert a $\bar k$-algebra isomorphism
of function fields to an isomorphism in `FunctionFieldObj`. -/
noncomputable def algEquivToFunctionFieldIso
    (F G : FunctionFieldObj k)
    (e : G.carrier ≃ₐ[AlgebraicClosure k] F.carrier) :
    F ≅ G where
  hom := ⟨e.toAlgHom⟩
  inv := ⟨e.symm.toAlgHom⟩
  hom_inv_id := by
    apply FunctionFieldObj.Hom.ext
    ext x
    show e (e.symm x) = x
    simp
  inv_hom_id := by
    apply FunctionFieldObj.Hom.ext
    ext x
    show e.symm (e x) = x
    simp

/-- Corollary 15.11 (forward direction). If $V$ and $W$ are birationally equivalent
affine varieties, then their function fields $\bar k(V)$ and $\bar k(W)$ are
isomorphic as $\bar k$-algebras. -/
end Corollary1511
