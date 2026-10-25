import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part9
open MvPolynomial
open MvPolynomial CategoryTheory


/--
[mem_denominatorIdeal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma mem_denominatorIdeal_iff
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [hdom : IsDomain (AffineCoordinateRingBar X)]
  {r : FractionRing (AffineCoordinateRingBar X)}
  {g : AffineCoordinateRingBar X} :
-- imply
  g ∈ denominatorIdeal r ↔ algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X)) g * r ∈ Set.range (algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X))) :=
-- proof
  Iff.rfl

/--
[mem_regularDomain_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma mem_regularDomain_iff
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [hdom : IsDomain (AffineCoordinateRingBar X)]
  {r : FractionRing (AffineCoordinateRingBar X)}
  {P : Fin n → AlgebraicClosure k} :
-- imply
  P ∈ regularDomain r ↔ ∃ (hP : P ∈ X), IsRegularAt r P hP :=
-- proof
  Iff.rfl

/--
[isRegularAt_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma isRegularAt_algebraMap
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [hdom : IsDomain (AffineCoordinateRingBar X)]
  {f : AffineCoordinateRingBar X}
  {P : Fin n → AlgebraicClosure k}
-- given
  (hP : P ∈ X) :
-- imply
  IsRegularAt (algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X)) f) P hP := by
-- proof
  refine ⟨1, ?_, ?_⟩
  · simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true]
  · simp only [map_one, one_mul]
    exact Set.mem_range_self f

/--
[regularDomain_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma regularDomain_algebraMap
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [hdom : IsDomain (AffineCoordinateRingBar X)]
  {f : AffineCoordinateRingBar X} :
-- imply
  regularDomain (algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X)) f) = X := by
-- proof
  ext P
  simp only [regularDomain, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, _⟩
    exact hP
  · intro hP
    exact ⟨hP, isRegularAt_algebraMap f P hP⟩

/--
[denominatorIdeal_eq_top_of_no_common_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma denominatorIdeal_eq_top_of_no_common_zero
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [hdom : IsDomain (AffineCoordinateRingBar X)]
  [Field k]
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  {J : Ideal (AffineCoordinateRingBar X)}
-- given
  (hAlg : IsAlgebraicSubset k n X)
  (hJ : ∀ (P : Fin n → AlgebraicClosure k) (hP : P ∈ X), ∃ g ∈ J, evalBarAtPoint k X P hP g ≠ 0) :
-- imply
  J = ⊤ := by
-- proof
  by_contra hJne
  set J' := Ideal.comap (Ideal.Quotient.mk (idealOfAlgebraicSet X)) J with hJ'_def
  have hJ'ne : J' ≠ ⊤ := by
    intro h
    apply hJne
    rw [Ideal.eq_top_iff_one] at h ⊢
    have : Ideal.Quotient.mk (idealOfAlgebraicSet X) 1 ∈ J := h
    rwa [map_one] at this
  obtain ⟨P, hPzero⟩ := weak_nullstellensatz k J' hJ'ne
  have hIX_le_J' : idealOfAlgebraicSet X ≤ J' := by
    intro x hx
    show Ideal.Quotient.mk (idealOfAlgebraicSet X) x ∈ J
    rwa [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have hP_in_ZIX : P ∈ AlgebraicSet k n ((idealOfAlgebraicSet X) : Set _) := by
    intro f hf
    exact hPzero f (hIX_le_J' hf)
  rw [algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset (k := k) hAlg] at hP_in_ZIX
  obtain ⟨g, hgJ, hgne⟩ := hJ P hP_in_ZIX
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  have hfJ' : f ∈ J' := by
    simp only [hJ'_def, Ideal.mem_comap]
    exact hgJ
  have heval_zero : eval P f = 0 := hPzero f hfJ'
  simp only [evalBarAtPoint_mk] at hgne
  exact hgne heval_zero

/--
[inRange_of_one_mem_denominatorIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma inRange_of_one_mem_denominatorIdeal
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [hdom : IsDomain (AffineCoordinateRingBar X)]
  {r : FractionRing (AffineCoordinateRingBar X)}
-- given
  (h : (1 : AffineCoordinateRingBar X) ∈ denominatorIdeal r) :
-- imply
  r ∈ Set.range (algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X))) := by
-- proof
  rw [mem_denominatorIdeal_iff] at h
  rwa [map_one, one_mul] at h

/--
[denominatorIdeal_eq_top_of_regularDomain_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma denominatorIdeal_eq_top_of_regularDomain_eq
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [hdom : IsDomain (AffineCoordinateRingBar X)]
  {r : FractionRing (AffineCoordinateRingBar X)}
-- given
  (hAlg : IsAlgebraicSubset k n X)
  (hdom : regularDomain r = X) :
-- imply
  denominatorIdeal r = ⊤ := by
-- proof
  apply denominatorIdeal_eq_top_of_no_common_zero hAlg
  intro P hP
  have hPreg : P ∈ regularDomain r := by rw [hdom]; exact hP
  obtain ⟨_, hreg⟩ := hPreg
  obtain ⟨g, hne, hmem⟩ := hreg
  exact ⟨g, hmem, hne⟩

/--
[regular_iff_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma regular_iff_polynomial
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [hdom : IsDomain (AffineCoordinateRingBar X)]
  {r : FractionRing (AffineCoordinateRingBar X)}
-- given
  (hAlg : IsAlgebraicSubset k n X) :
-- imply
  r ∈ Set.range (algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X))) ↔ regularDomain r = X := by
-- proof
  constructor
  ·
    rintro ⟨f, rfl⟩
    exact regularDomain_algebraMap f
  ·
    intro hdom
    have h1 : denominatorIdeal r = ⊤ :=
      denominatorIdeal_eq_top_of_regularDomain_eq hAlg r hdom
    have h1mem : (1 : AffineCoordinateRingBar X) ∈ denominatorIdeal r := by
      rw [h1]; exact Submodule.mem_top
    exact inRange_of_one_mem_denominatorIdeal r h1mem
section RationalMaps
variable {k : Type*} [Field k]
variable {m n_cod : ℕ}
variable {X : Set (Fin m → AlgebraicClosure k)}
variable [hdom : IsDomain (AffineCoordinateRingBar X)]
open MvPolynomial

/--
[rationalMapDomain_eq_inter_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma rationalMapDomain_eq_inter_iInter
  {k : Type*}
  [Field k]
  [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  [hdom : IsDomain (AffineCoordinateRingBar X)]
  {φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)} :
-- imply
  rationalMapDomain φ = X ∩ ⋂ i, regularDomain (φ i) := by
-- proof
  ext P
  simp only [rationalMapDomain, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_iInter, mem_regularDomain_iff, IsTupleRegularAt]
  constructor
  · rintro ⟨hP, hall⟩
    exact ⟨hP, fun i => ⟨hP, hall i⟩⟩
  · rintro ⟨hP, hall⟩
    exact ⟨hP, fun i => (hall i).2⟩

/--
[dominantPullbackToFractionRing_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma dominantPullbackToFractionRing_mk
  {k : Type*}
  [Field k]
  [Field k]
  [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  {Y : Set (Fin n_cod → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  [IsDomain (AffineCoordinateRingBar Y)]
  {φ : AffineRationalMap X Y}
  {f : MvPolynomial (Fin n_cod) (AlgebraicClosure k)} :
-- imply
  dominantPullbackToFractionRing φ (Ideal.Quotient.mk _ f) = dominantPullbackSubstHom φ.components f :=
-- proof
  Ideal.Quotient.lift_mk _ _ _

variable (k : Type*) [Field k]
variable [Field k]
/--
[eval₂_clearing_denominators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
any polynomial $f \in \bar k[Y_1, \dots, Y_{n_\mathrm{cod}}]$ and any point $P$ at which
the components $(\theta(Y_1), \dots, \theta(Y_{n_\mathrm{cod}}))$ are all regular, there
exist $g_0, f_0 \in \bar k[X]$ with $g_0(P) \neq 0$ such that
$\theta_*(f) = f_0 / g_0$ in $\bar k(X)$ and $f(\theta(P)) \cdot g_0(P) = f_0(P)$. -/
lemma eval₂_clearing_denominators
  {k : Type*} [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  {Y : Set (Fin n_cod → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  [IsDomain (AffineCoordinateRingBar Y)]
  (θ : FractionRing (AffineCoordinateRingBar Y) →+*
    FractionRing (AffineCoordinateRingBar X))
  (hθ : IsKbarFunctionFieldHom θ)
  (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
  (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP)
  (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k)) :
  ∃ (g₀ : AffineCoordinateRingBar X) (f₀ : AffineCoordinateRingBar X),
    evalBarAtPoint k X P hP g₀ ≠ 0 ∧
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) f₀ =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) g₀ *
      MvPolynomial.eval₂
        ((algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))).comp
          ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C))
        (functionFieldMorphismComponents θ) f ∧
    MvPolynomial.eval (evalTupleAt (functionFieldMorphismComponents θ) P hP hreg) f *
      evalBarAtPoint k X P hP g₀ = evalBarAtPoint k X P hP f₀ := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    refine ⟨1, Ideal.Quotient.mk _ (MvPolynomial.C c), ?_, ?_, ?_⟩
    · simp [map_one]
    · simp [MvPolynomial.eval₂_C, RingHom.comp_apply, map_one, one_mul]; rfl
    · simp [MvPolynomial.eval_C, map_one, mul_one, evalBarAtPoint_mk]
  | add p q ihp ihq =>
    obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
    obtain ⟨gq, fq, hgq_ne, hfq_eq, hfq_eval⟩ := ihq
    refine ⟨gp * gq, gq * fp + gp * fq, ?_, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hgp_ne hgq_ne
    · simp only [map_mul, map_add, MvPolynomial.eval₂_add]
      rw [mul_add]
      congr 1
      · rw [hfp_eq]; ring
      · rw [hfq_eq]; ring
    · simp only [map_mul, map_add]
      linear_combination (evalBarAtPoint k X P hP gq) * hfp_eval +
        (evalBarAtPoint k X P hP gp) * hfq_eval
  | mul_X p j ihp =>
    obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
    obtain ⟨gj, hgj_ne, hgj_mem⟩ := hreg j
    obtain ⟨aj, haj_eq⟩ := hgj_mem
    refine ⟨gp * gj, fp * aj, ?_, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hgp_ne hgj_ne
    · simp only [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      rw [mul_comm (algebraMap _ _ gp) (algebraMap _ _ gj), mul_assoc (algebraMap _ _ gj),
        ← mul_assoc (algebraMap _ _ gp)]
      rw [hfp_eq]
      rw [mul_assoc, mul_comm (MvPolynomial.eval₂ _ _ p), ← mul_assoc, haj_eq]
      ring
    · simp only [MvPolynomial.eval_X, map_mul]
      have hσj : evalTupleAt (functionFieldMorphismComponents θ) P hP hreg j *
        evalBarAtPoint k X P hP gj = evalBarAtPoint k X P hP aj := by
        unfold evalTupleAt
        rw [evalRatFunAt_eq (functionFieldMorphismComponents θ j) P hP (hreg j) gj aj hgj_ne haj_eq.symm]
        rw [div_mul_cancel₀ _ hgj_ne]
      calc (MvPolynomial.eval _ p) *
        (evalTupleAt (functionFieldMorphismComponents θ) P hP hreg j) *
        ((evalBarAtPoint k X P hP gp) * (evalBarAtPoint k X P hP gj))
        = ((MvPolynomial.eval _ p) * (evalBarAtPoint k X P hP gp)) *
          ((evalTupleAt (functionFieldMorphismComponents θ) P hP hreg j) *
            (evalBarAtPoint k X P hP gj)) := by ring
        _ = (evalBarAtPoint k X P hP fp) * (evalBarAtPoint k X P hP aj) := by
          rw [hfp_eval, hσj]

variable (k : Type*) [Field k]
variable [Field k]
/--
[theta_algebraMap_mk_eq_eval₂](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
applying $\theta$ to the class of $f \in \bar k[Y]$ in $\bar k(Y)$ equals evaluating $f$
via substitution at the components $\theta(Y_i)$. -/
lemma theta_algebraMap_mk_eq_eval₂
  {k : Type*} [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  {Y : Set (Fin n_cod → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  [IsDomain (AffineCoordinateRingBar Y)]
  (θ : FractionRing (AffineCoordinateRingBar Y) →+*
    FractionRing (AffineCoordinateRingBar X))
  (hθ : IsKbarFunctionFieldHom θ)
  (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k)) :
  θ ((algebraMap (AffineCoordinateRingBar Y)
    (FractionRing (AffineCoordinateRingBar Y)))
    (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) =
  MvPolynomial.eval₂
    ((algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
      ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C))
    (functionFieldMorphismComponents θ) f := by
  let ϕ : MvPolynomial (Fin n_cod) (AlgebraicClosure k) →+*
    FractionRing (AffineCoordinateRingBar X) :=
    θ.comp ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y))).comp
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y)))
  have h := MvPolynomial.map_mvPolynomial_eq_eval₂ ϕ f
  change θ _ = _ at h
  rw [show (ϕ.comp MvPolynomial.C) =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
      ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C) from
    RingHom.ext (fun c => hθ c)] at h
  rw [show (fun s => ϕ (MvPolynomial.X s)) = functionFieldMorphismComponents θ from
    funext (fun j => rfl)] at h
  exact h

/--
[fractionRing_element_zero_of_eval_zero_on_tupleRegular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma fractionRing_element_zero_of_eval_zero_on_tupleRegular
  {k : Type*}
  [Field k]
  [Field k]
  [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  {r : FractionRing (AffineCoordinateRingBar X)}
  {φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)}
-- given
  (h : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X) (hreg_comp : IsTupleRegularAt φ P hP) (hreg : IsRegularAt r P hP), evalRatFunAt r P hP hreg = 0) :
-- imply
  r = 0 := by
-- proof
  by_contra hr
  obtain ⟨⟨a_r, ⟨b_r, hb_r⟩⟩, hab_r⟩ := IsLocalization.surj
    (nonZeroDivisors (AffineCoordinateRingBar X)) r
  simp only at hab_r
  have ha_ne : a_r ≠ 0 := by
    intro ha0; apply hr
    have h1 : r * (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) b_r = 0 := by
      rw [hab_r, ha0, map_zero]
    have hb_ne_frac : (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) b_r ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      exact mem_nonZeroDivisors_iff_ne_zero.mp hb_r
    exact (mul_eq_zero.mp h1).resolve_right hb_ne_frac
  have hb_ne : b_r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_r
  choose cd_j hcd_j using
    (fun j => IsLocalization.surj (nonZeroDivisors (AffineCoordinateRingBar X)) (φ j))
  set product := a_r * (b_r * ∏ j : Fin n_cod, ((cd_j j).2 : AffineCoordinateRingBar X))
    with hprod_def
  have hprod_ne : product ≠ 0 := by
    apply mul_ne_zero ha_ne (mul_ne_zero hb_ne _)
    exact Finset.prod_ne_zero_iff.mpr (fun j _ =>
      mem_nonZeroDivisors_iff_ne_zero.mp (cd_j j).2.property)
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
    push_neg at hdP
    have hab_comm : (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) b_r * r =
      (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) a_r := by rw [mul_comm]; exact hab_r
    have hreg : IsRegularAt r P hP :=
      ⟨b_r, hbP, ⟨a_r, hab_comm.symm⟩⟩
    have hreg_comp : IsTupleRegularAt φ P hP := by
      intro j
      exact ⟨((cd_j j).2 : AffineCoordinateRingBar X), hdP j,
        ⟨(cd_j j).1, ((hcd_j j).symm.trans (mul_comm _ _))⟩⟩
    have h_eval_zero := h P hP hreg_comp hreg
    have h_eq := evalRatFunAt_eq r P hP hreg b_r a_r hbP hab_comm
    rw [h_eq] at h_eval_zero
    have haP : evalBarAtPoint k X P hP a_r = 0 := by
      obtain haP | hbP' := div_eq_zero_iff.mp h_eval_zero
      · exact haP
      · exact absurd hbP' hbP
    simp [haP]
  have hprod_zero : product = 0 := by
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective product
    suffices h_mem : f ∈ idealOfAlgebraicSet X by
      rw [← hf]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h_mem
    rw [mem_idealOfAlgebraicSet_iff]
    intro P hP
    have := hprod_vanishes P hP
    rwa [← hf, evalBarAtPoint_mk] at this
  exact hprod_ne hprod_zero

/--
[functionFieldMorphismInducedMap_isDominant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma functionFieldMorphismInducedMap_isDominant
  {k : Type*}
  [Field k]
  [Field k]
  [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  {Y : Set (Fin n_cod → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  [IsDomain (AffineCoordinateRingBar Y)]
  {θ : FractionRing (AffineCoordinateRingBar Y) →+* FractionRing (AffineCoordinateRingBar X)}
-- given
  (hθ : IsKbarFunctionFieldHom θ)
  (hY : IsAlgebraicSubset k n_cod Y) :
-- imply
  IsDominantRationalMap Y (functionFieldMorphismInducedMap θ hθ hY) := by
-- proof
  unfold IsDominantRationalMap
  apply Set.Subset.antisymm
  · intro Q hQ
    simp only [zariskiClosure, AlgebraicSet, Set.mem_setOf_eq, SetLike.mem_coe,
      mem_idealOfAlgebraicSet_iff] at hQ
    rw [← algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hY]
    intro f hf
    apply hQ
    intro R hR
    obtain ⟨P, hP, hreg, rfl⟩ := hR
    exact hf _ (functionFieldMorphism_image_mem θ hθ hY P hP hreg)
  · intro Q hQ
    simp only [zariskiClosure, AlgebraicSet, Set.mem_setOf_eq, SetLike.mem_coe,
      mem_idealOfAlgebraicSet_iff]
    intro f hf_vanishes_on_image
    have hθf_zero : θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) = 0 := by
      apply fractionRing_element_zero_of_eval_zero_on_tupleRegular
        _ (functionFieldMorphismComponents θ)
      intro P hP hreg_comp hreg_θf
      rw [← characterizing_property θ hθ f P hP hreg_comp hreg_θf]
      apply hf_vanishes_on_image
      exact ⟨P, hP, hreg_comp, rfl⟩
    have hf_bar_zero : (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f :
      AffineCoordinateRingBar Y) = 0 := by
      have h_alg_zero : (algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f) = 0 := by
        have h_inj := θ.injective
        exact h_inj (by rw [hθf_zero, map_zero])
      rwa [map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h_alg_zero
    have hf_mem : f ∈ idealOfAlgebraicSet Y :=
      Ideal.Quotient.eq_zero_iff_mem.mp hf_bar_zero
    exact hf_mem Q hQ
/-- Compatibility of coordinate-ring pullbacks with composition: if $\psi \circ \varphi$
is a rational map matching the formal composition of pullbacks on coordinates, then
$(\psi \circ \varphi)^* = \varphi^* \circ \psi^*$ as ring maps $\bar k[Z] \to \bar k[X]$. -/
section Corollary1512
variable {k : Type*} [Field k]
open MvPolynomial

/--
[AffineVarietyDom.idMap_dominant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma AffineVarietyDom.idMap_dominant
  {k : Type*}
  [Field k]
  {k : Type*}
  [Field k]
  [Field k]
  {V : AffineVarietyDom k} :
-- imply
  @IsDominantRationalMap k _ V.dim V.dim V.carrier V.isDomain V.carrier (AffineVarietyDom.idMap V) :=
-- proof
  @functionFieldMorphismInducedMap_isDominant k _ V.dim V.dim V.carrier V.carrier V.isDomain V.isDomain
    (RingHom.id _) (fun _ => rfl) V.isAlgebraic

/--
[algHom_isKbarFunctionFieldHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
lemma algHom_isKbarFunctionFieldHom
  {k : Type*}
  [Field k]
  {k : Type*}
  [Field k]
  [Field k]
  {V W : AffineVarietyDom k}
  {θ : FractionRing (AffineCoordinateRingBar W.carrier) →ₐ[AlgebraicClosure k] FractionRing (AffineCoordinateRingBar V.carrier)} :
-- imply
  IsKbarFunctionFieldHom θ.toRingHom := by
-- proof
  intro r
  have h := θ.commutes r
  change θ (algebraMap (AffineCoordinateRingBar W.carrier)
    (FractionRing (AffineCoordinateRingBar W.carrier))
    (Ideal.Quotient.mk (idealOfAlgebraicSet W.carrier) (MvPolynomial.C r))) =
    algebraMap (AffineCoordinateRingBar V.carrier)
    (FractionRing (AffineCoordinateRingBar V.carrier))
    (Ideal.Quotient.mk (idealOfAlgebraicSet V.carrier) (MvPolynomial.C r))
  rw [show (Ideal.Quotient.mk (idealOfAlgebraicSet W.carrier) (MvPolynomial.C r) : AffineCoordinateRingBar W.carrier) = algebraMap (AlgebraicClosure k) (AffineCoordinateRingBar W.carrier) r from rfl]
  rw [show (Ideal.Quotient.mk (idealOfAlgebraicSet V.carrier) (MvPolynomial.C r) : AffineCoordinateRingBar V.carrier) = algebraMap (AlgebraicClosure k) (AffineCoordinateRingBar V.carrier) r from rfl]
  rw [← IsScalarTower.algebraMap_apply (AlgebraicClosure k) (AffineCoordinateRingBar W.carrier) (FractionRing (AffineCoordinateRingBar W.carrier))]
  rwa [← IsScalarTower.algebraMap_apply (AlgebraicClosure k) (AffineCoordinateRingBar V.carrier) (FractionRing (AffineCoordinateRingBar V.carrier))]
/-- Categorical version of the morphisms roundtrip: starting from a $\bar k$-algebra
homomorphism $\theta : \bar k(W) \to \bar k(V)$, taking the induced rational map and
then its function-field pullback recovers $\theta$. -/
section Corollary1511
variable (k : Type*) [Field k]
open MvPolynomial CategoryTheory

/--
[evalBarAtPoint_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
private lemma evalBarAtPoint_mk_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  {P : Fin n → AlgebraicClosure k}
  {f : MvPolynomial (Fin n) (AlgebraicClosure k)}
-- given
  (hP : P ∈ X) :
-- imply
  evalBarAtPoint k X P hP (Ideal.Quotient.mk _ f) = eval P f := by
-- proof
  apply evalBarAtPoint_mk k X P hP f

/--
[dominantPullbackSubstHom_kills_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
private lemma dominantPullbackSubstHom_kills_ideal_eq
  {k : Type*}
  [Field k]
  [Field k]
  [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  {Y : Set (Fin n_cod → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  [IsDomain (AffineCoordinateRingBar Y)]
  {φ : AffineRationalMap X Y}
  {f : MvPolynomial (Fin n_cod) (AlgebraicClosure k)}
-- given
  (hf : f ∈ idealOfAlgebraicSet Y) :
-- imply
  dominantPullbackSubstHom φ.components f = 0 := by
-- proof
  apply dominantPullbackSubstHom_kills_ideal k φ f hf

/--
[evalRatFunAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
private lemma evalRatFunAt_eq_eq
  {k : Type*}
  [Field k]
  [Field k]
  [Field k]
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  {r : FractionRing (AffineCoordinateRingBar X)}
  {P : Fin n → AlgebraicClosure k}
  {g f_val : AffineCoordinateRingBar X}
-- given
  (hP : P ∈ X)
  (hreg : IsRegularAt r P hP)
  (hg_ne : evalBarAtPoint k X P hP g ≠ 0)
  (hgr : algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X)) g * r = algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X)) f_val) :
-- imply
  evalRatFunAt r P hP hreg = evalBarAtPoint k X P hP f_val / evalBarAtPoint k X P hP g := by
-- proof
  apply evalRatFunAt_eq k r P hP hreg g f_val hg_ne hgr

/--
[eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
private lemma eval_eq
  {k : Type*}
  [Field k]
  [Field k]
  [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  {Y : Set (Fin n_cod → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  [IsDomain (AffineCoordinateRingBar Y)]
  {θ : FractionRing (AffineCoordinateRingBar Y) →+* FractionRing (AffineCoordinateRingBar X)}
  {P : Fin m → AlgebraicClosure k}
  {f : MvPolynomial (Fin n_cod) (AlgebraicClosure k)}
-- given
  (hθ : IsKbarFunctionFieldHom θ)
  (hP : P ∈ X)
  (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP) :
-- imply
  ∃ (g₀ : AffineCoordinateRingBar X) (f₀ : AffineCoordinateRingBar X), evalBarAtPoint k X P hP g₀ ≠ 0 ∧ (algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X))) f₀ = (algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X))) g₀ * MvPolynomial.eval₂ ((algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X))).comp ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C)) (functionFieldMorphismComponents θ) f ∧ MvPolynomial.eval (evalTupleAt (functionFieldMorphismComponents θ) P hP hreg) f * evalBarAtPoint k X P hP g₀ = evalBarAtPoint k X P hP f₀ := by
-- proof
  apply eval k θ hθ P hP hreg f

/--
[theta_algebraMap_mk_eq_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
private lemma theta_algebraMap_mk_eq_eval_eq
  {k : Type*}
  [Field k]
  [Field k]
  [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  {Y : Set (Fin n_cod → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  [IsDomain (AffineCoordinateRingBar Y)]
  {θ : FractionRing (AffineCoordinateRingBar Y) →+* FractionRing (AffineCoordinateRingBar X)}
  {f : MvPolynomial (Fin n_cod) (AlgebraicClosure k)}
-- given
  (hθ : IsKbarFunctionFieldHom θ) :
-- imply
  θ ((algebraMap (AffineCoordinateRingBar Y) (FractionRing (AffineCoordinateRingBar Y))) (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) = MvPolynomial.eval₂ ((algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X))).comp ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C)) (functionFieldMorphismComponents θ) f := by
-- proof
  apply theta_algebraMap_mk_eq_eval k θ hθ f

/--
[characterizing_property](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
private lemma characterizing_property_eq
  {k : Type*}
  [Field k]
  [Field k]
  [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  {Y : Set (Fin n_cod → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  [IsDomain (AffineCoordinateRingBar Y)]
  {θ : FractionRing (AffineCoordinateRingBar Y) →+* FractionRing (AffineCoordinateRingBar X)}
  {f : MvPolynomial (Fin n_cod) (AlgebraicClosure k)}
  {P : Fin m → AlgebraicClosure k}
-- given
  (hθ : IsKbarFunctionFieldHom θ)
  (hP : P ∈ X)
  (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP)
  (hreg_θf : IsRegularAt (θ ((algebraMap (AffineCoordinateRingBar Y) (FractionRing (AffineCoordinateRingBar Y))) (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f))) P hP) :
-- imply
  MvPolynomial.eval (evalTupleAt (functionFieldMorphismComponents θ) P hP hreg) f = evalRatFunAt (θ ((algebraMap (AffineCoordinateRingBar Y) (FractionRing (AffineCoordinateRingBar Y))) (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f))) P hP hreg_θf := by
-- proof
  apply characterizing_property k θ hθ f P hP hreg hreg_θf

/--
[isRegularAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
private lemma isRegularAt_zero_eq
  {k : Type*}
  [Field k]
  [Field k]
  {m : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  {P : Fin m → AlgebraicClosure k}
-- given
  (hP : P ∈ X) :
-- imply
  IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP := by
-- proof
  apply isRegularAt_zero k P hP

/--
[evalRatFunAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
private lemma evalRatFunAt_zero_eq
  {k : Type*}
  [Field k]
  [Field k]
  {m : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  {P : Fin m → AlgebraicClosure k}
-- given
  (hP : P ∈ X)
  (hreg : IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP) :
-- imply
  evalRatFunAt 0 P hP hreg = 0 := by
-- proof
  apply evalRatFunAt_zero k P hP hreg

/--
[functionFieldMorphism_image_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
private lemma functionFieldMorphism_image_mem_eq
  {k : Type*}
  [Field k]
  [Field k]
  {m n_cod : ℕ}
  {X : Set (Fin m → AlgebraicClosure k)}
  {Y : Set (Fin n_cod → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  [IsDomain (AffineCoordinateRingBar Y)]
  {θ : FractionRing (AffineCoordinateRingBar Y) →+* FractionRing (AffineCoordinateRingBar X)}
  {P : Fin m → AlgebraicClosure k}
-- given
  (hθ : IsKbarFunctionFieldHom θ)
  (hY : IsAlgebraicSubset k n_cod Y)
  (hP : P ∈ X)
  (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP) :
-- imply
  evalTupleAt (functionFieldMorphismComponents θ) P hP hreg ∈ Y := by
-- proof
  apply functionFieldMorphism_image_mem k θ hθ hY P hP hreg

/--
[coordRingToBar_comp_algebraMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean)
-/
@[path]
private lemma coordRingToBar_comp_algebraMap_injective_eq
  {k : Type*}
  [Field k]
  [Field k]
  [Field k]
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  [IsDomain (AffineCoordinateRingBar X)]
  [IsDomain (AffineCoordinateRing X)] :
-- imply
  Function.Injective ((algebraMap (AffineCoordinateRingBar X) (FractionRing (AffineCoordinateRingBar X))).comp (coordRingToBar X)) := by
-- proof
  apply coordRingToBar_comp_algebraMap_injective k X


-- created on 2026-10-23
