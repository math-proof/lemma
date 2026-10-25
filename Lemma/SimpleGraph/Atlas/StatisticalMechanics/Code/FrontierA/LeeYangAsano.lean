import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part15
open StatMech StatMech.FrontierA


/--
[asano_quadratic_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma asano_quadratic_contraction_eq
  {A E D z : ℂ}
-- given
  (hstable : ∀ t : ℂ, ‖t‖ < 1 → A + E * t + D * t ^ 2 ≠ 0)
  (hz : ‖z‖ < 1) :
-- imply
  A + D * z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.asano_quadratic_contraction A E D z hstable hz

/--
[asanoContract_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma asanoContract_stable_eq
  [DecidableEq I]
  {p : (I → ℂ) → ℂ}
  {i j : I}
-- given
  (hpAff : IsMultiAffine p)
  (hpStable : PolydiscStable p)
  (hij : i ≠ j) :
-- imply
  PolydiscStable (asanoContract p i j) := by
-- proof
  apply StatMech.FrontierA.asanoContract_stable p hpAff hpStable hij

/--
[asanoContract_multiAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma asanoContract_multiAffine_eq
  [DecidableEq I]
  {p : (I → ℂ) → ℂ}
  {i j : I}
-- given
  (hp : IsMultiAffine p)
  (hij : i ≠ j) :
-- imply
  IsMultiAffine (asanoContract p i j) := by
-- proof
  apply StatMech.FrontierA.asanoContract_multiAffine p hp hij

/--
[leeYang_edgeFactor_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYang_edgeFactor_ne_zero_eq
  {r : ℝ}
  {a b : ℂ}
-- given
  (hr0 : 0 ≤ r)
  (hr1 : r ≤ 1)
  (ha : ‖a‖ < 1)
  (hb : ‖b‖ < 1) :
-- imply
  1 + a * b + (r : ℂ) * (a + b) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.leeYang_edgeFactor_ne_zero hr0 hr1 ha hb

/--
[leeYangHalfEdgeProduct_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangHalfEdgeProduct_eq_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : LeeYangVar G → ℂ} :
-- imply
  leeYangHalfEdgeProduct G beta z = leeYangAnchorProduct G z * leeYangEdgeProduct G beta z := by
-- proof
  apply StatMech.FrontierA.leeYangHalfEdgeProduct_eq beta z

/--
[leeYangNormalizedEdgeFactor_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangNormalizedEdgeFactor_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {e : ↑G.edgeFinset}
  {z : LeeYangVar G → ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hz : ∀ i, ‖z i‖ < 1) :
-- imply
  leeYangNormalizedEdgeFactor G beta e z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.leeYangNormalizedEdgeFactor_ne_zero hbeta e z hz

/--
[leeYangHalfEdgeProduct_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangHalfEdgeProduct_stable_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  PolydiscStable (leeYangHalfEdgeProduct G beta) := by
-- proof
  apply StatMech.FrontierA.leeYangHalfEdgeProduct_stable hbeta

/--
[leeYangNormalizedEdgeFactor_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangNormalizedEdgeFactor_affine_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {e : ↑G.edgeFinset}
  {w : V}
  {z : LeeYangVar G → ℂ}
  {t : ℂ} :
-- imply
  leeYangNormalizedEdgeFactor G beta e (Function.update z (leeYangHalf G w e) t) = leeYangNormalizedEdgeFactor G beta e (Function.update z (leeYangHalf G w e) 0) + t * (leeYangNormalizedEdgeFactor G beta e (Function.update z (leeYangHalf G w e) 1) - leeYangNormalizedEdgeFactor G beta e (Function.update z (leeYangHalf G w e) 0)) := by
-- proof
  apply StatMech.FrontierA.leeYangNormalizedEdgeFactor_affine beta e w z t

/--
[leeYangNormalizedEdgeFactor_update_other](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangNormalizedEdgeFactor_update_other_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {e e' : ↑G.edgeFinset}
  {w : V}
  {z : LeeYangVar G → ℂ}
  {t : ℂ}
-- given
  (hee : e' ≠ e) :
-- imply
  leeYangNormalizedEdgeFactor G beta e (Function.update z (leeYangHalf G w e') t) = leeYangNormalizedEdgeFactor G beta e z := by
-- proof
  apply StatMech.FrontierA.leeYangNormalizedEdgeFactor_update_other beta hee w z t

/--
[leeYangNormalizedEdgeFactor_update_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangNormalizedEdgeFactor_update_anchor_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {e : ↑G.edgeFinset}
  {w : V}
  {z : LeeYangVar G → ℂ}
  {t : ℂ} :
-- imply
  leeYangNormalizedEdgeFactor G beta e (Function.update z (leeYangAnchor G w) t) = leeYangNormalizedEdgeFactor G beta e z := by
-- proof
  apply StatMech.FrontierA.leeYangNormalizedEdgeFactor_update_anchor beta e w z t

/--
[leeYangAnchorProduct_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangAnchorProduct_affine_eq
  [Fintype V]
  [DecidableEq V]
  {w : V}
  {z : LeeYangVar G → ℂ}
  {t : ℂ} :
-- imply
  leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) t) = leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) 0) + t * (leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) 1) - leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) 0)) := by
-- proof
  apply StatMech.FrontierA.leeYangAnchorProduct_affine w z t

/--
[leeYangAnchorProduct_update_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangAnchorProduct_update_half_eq
  [Fintype V]
  [DecidableEq V]
  {w : V}
  {e : ↑G.edgeFinset}
  {z : LeeYangVar G → ℂ}
  {t : ℂ} :
-- imply
  leeYangAnchorProduct G (Function.update z (leeYangHalf G w e) t) = leeYangAnchorProduct G z := by
-- proof
  apply StatMech.FrontierA.leeYangAnchorProduct_update_half w e z t

/--
[leeYangEdgeProduct_update_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangEdgeProduct_update_anchor_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {w : V}
  {z : LeeYangVar G → ℂ}
  {t : ℂ} :
-- imply
  leeYangEdgeProduct G beta (Function.update z (leeYangAnchor G w) t) = leeYangEdgeProduct G beta z := by
-- proof
  apply StatMech.FrontierA.leeYangEdgeProduct_update_anchor beta w z t

/--
[leeYangEdgeProduct_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangEdgeProduct_affine_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {w : V}
  {e : ↑G.edgeFinset}
  {z : LeeYangVar G → ℂ}
  {t : ℂ} :
-- imply
  leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) t) = leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) 0) + t * (leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) 1) - leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) 0)) := by
-- proof
  apply StatMech.FrontierA.leeYangEdgeProduct_affine beta w e z t

/--
[leeYangHalfEdgeProduct_multiAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangHalfEdgeProduct_multiAffine_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  IsMultiAffine (leeYangHalfEdgeProduct G beta) := by
-- proof
  apply StatMech.FrontierA.leeYangHalfEdgeProduct_multiAffine beta

/--
[leeYangContractList_multiAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractList_multiAffine_eq
  [Fintype V]
  [DecidableEq V]
  {L : List (V × ↑G.edgeFinset)}
  {p : (LeeYangVar G → ℂ) → ℂ}
-- given
  (hp : IsMultiAffine p) :
-- imply
  IsMultiAffine (leeYangContractList G L p) := by
-- proof
  apply StatMech.FrontierA.leeYangContractList_multiAffine L p hp

/--
[leeYangContractList_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractList_stable_eq
  [Fintype V]
  [DecidableEq V]
  {L : List (V × ↑G.edgeFinset)}
  {p : (LeeYangVar G → ℂ) → ℂ}
-- given
  (hpAff : IsMultiAffine p)
  (hpStable : PolydiscStable p) :
-- imply
  PolydiscStable (leeYangContractList G L p) := by
-- proof
  apply StatMech.FrontierA.leeYangContractList_stable L p hpAff hpStable

/--
[leeYangContractedProduct_multiAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractedProduct_multiAffine_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  IsMultiAffine (leeYangContractedProduct G beta) := by
-- proof
  apply StatMech.FrontierA.leeYangContractedProduct_multiAffine beta

/--
[leeYangContractedProduct_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractedProduct_stable_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  PolydiscStable (leeYangContractedProduct G beta) := by
-- proof
  apply StatMech.FrontierA.leeYangContractedProduct_stable hbeta

/--
[leeYangMonomial_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangMonomial_update_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq I]
  {S : Finset I}
  {z : I → ℂ}
  {i : I}
  {u : ℂ} :
-- imply
  leeYangMonomial S (Function.update z i u) = if i ∈ S then u * leeYangMonomial (S.erase i) z else leeYangMonomial S z := by
-- proof
  apply StatMech.FrontierA.leeYangMonomial_update S z i u

/--
[asanoContract_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma asanoContract_add_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq I]
  {p q : (I → ℂ) → ℂ}
  {i j : I} :
-- imply
  asanoContract (fun z ↦ p z + q z) i j = fun z ↦ asanoContract p i j z + asanoContract q i j z := by
-- proof
  apply StatMech.FrontierA.asanoContract_add p q i j

/--
[asanoContract_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma asanoContract_sum_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq I]
  [DecidableEq A]
  {s : Finset A}
  {p : A → (I → ℂ) → ℂ}
  {i j : I} :
-- imply
  asanoContract (fun z ↦ ∑ a ∈ s, p a z) i j = fun z ↦ ∑ a ∈ s, asanoContract (p a) i j z := by
-- proof
  apply StatMech.FrontierA.asanoContract_sum s p i j

/--
[asanoContract_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma asanoContract_monomial_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq I]
  {S : Finset I}
  {z : I → ℂ}
  {i j : I}
-- given
  (hij : i ≠ j) :
-- imply
  asanoContract (leeYangMonomial S) i j z = if (i ∈ S ↔ j ∈ S) then leeYangMonomial (S.erase j) z else 0 := by
-- proof
  apply StatMech.FrontierA.asanoContract_monomial S z hij

/--
[leeYang_endpoints_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYang_endpoints_mk_eq
  [Fintype V]
  [DecidableEq V]
  {e : ↑G.edgeFinset} :
-- imply
  s(leeYangEndpoint0 G e, leeYangEndpoint1 G e) = e.1 := by
-- proof
  apply StatMech.FrontierA.leeYang_endpoints_mk e

/--
[leeYang_endpoints_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYang_endpoints_ne_eq
  [Fintype V]
  [DecidableEq V]
  {e : ↑G.edgeFinset} :
-- imply
  leeYangEndpoint0 G e ≠ leeYangEndpoint1 G e := by
-- proof
  apply StatMech.FrontierA.leeYang_endpoints_ne e

/--
[sum_leeYangAnchorChoiceFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma sum_leeYangAnchorChoiceFactor_eq
  [Fintype V]
  [DecidableEq V]
  {z : LeeYangVar G → ℂ}
  {v : V} :
-- imply
  ∑ b : Bool, leeYangAnchorChoiceFactor G z v b = 1 + z (leeYangAnchor G v) := by
-- proof
  apply StatMech.FrontierA.sum_leeYangAnchorChoiceFactor z v

/--
[sum_leeYangEdgeChoiceFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma sum_leeYangEdgeChoiceFactor_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : LeeYangVar G → ℂ}
  {e : ↑G.edgeFinset} :
-- imply
  ∑ b : Bool × Bool, leeYangEdgeChoiceFactor G beta z e b = leeYangNormalizedEdgeFactor G beta e z := by
-- proof
  apply StatMech.FrontierA.sum_leeYangEdgeChoiceFactor beta z e

/--
[leeYangHalfEdgeProduct_eq_sum_choices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangHalfEdgeProduct_eq_sum_choices_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  leeYangHalfEdgeProduct G beta = fun z ↦ ∑ x : (V → Bool) × (↑G.edgeFinset → Bool × Bool), leeYangChoiceTerm G beta x z := by
-- proof
  apply StatMech.FrontierA.leeYangHalfEdgeProduct_eq_sum_choices beta

/--
[leeYangChoiceTerm_eq_weight_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangChoiceTerm_eq_weight_monomial_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)}
  {z : LeeYangVar G → ℂ} :
-- imply
  leeYangChoiceTerm G beta x z = leeYangChoiceWeight G beta x * leeYangMonomial (leeYangChoiceSupport G x) z := by
-- proof
  apply StatMech.FrontierA.leeYangChoiceTerm_eq_weight_monomial beta x z

/--
[asanoContract_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma asanoContract_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq I]
  {c : ℂ}
  {p : (I → ℂ) → ℂ}
  {i j : I} :
-- imply
  asanoContract (fun z ↦ c * p z) i j = fun z ↦ c * asanoContract p i j z := by
-- proof
  apply StatMech.FrontierA.asanoContract_const_mul c p i j

/--
[leeYangContractList_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractList_zero_eq
  [Fintype V]
  [DecidableEq V]
  {L : List (V × ↑G.edgeFinset)} :
-- imply
  leeYangContractList G L (fun _ ↦ 0) = fun _ ↦ 0 := by
-- proof
  apply StatMech.FrontierA.leeYangContractList_zero L

/--
[leeYangContractList_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractList_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {L : List (V × ↑G.edgeFinset)}
  {c : ℂ}
  {p : (LeeYangVar G → ℂ) → ℂ} :
-- imply
  leeYangContractList G L (fun z ↦ c * p z) = fun z ↦ c * leeYangContractList G L p z := by
-- proof
  apply StatMech.FrontierA.leeYangContractList_const_mul L c p

/--
[leeYangContractList_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractList_monomial_eq
  [Fintype V]
  [DecidableEq V]
  {L : List (V × ↑G.edgeFinset)}
  {S : Finset (LeeYangVar G)}
  {z : LeeYangVar G → ℂ}
-- given
  (hL : L.Nodup) :
-- imply
  leeYangContractList G L (leeYangMonomial S) z = if LeeYangConsistent G L S then leeYangMonomial (leeYangEraseHalves G L S) z else 0 := by
-- proof
  apply StatMech.FrontierA.leeYangContractList_monomial L hL S z

/--
[leeYangContractList_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractList_sum_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype A]
  [DecidableEq A]
  {L : List (V × ↑G.edgeFinset)}
  {p : A → (LeeYangVar G → ℂ) → ℂ} :
-- imply
  leeYangContractList G L (fun z ↦ ∑ a : A, p a z) = fun z ↦ ∑ a : A, leeYangContractList G L (p a) z := by
-- proof
  apply StatMech.FrontierA.leeYangContractList_sum L p

/--
[leeYangAnchor_mem_choiceSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangAnchor_mem_choiceSupport_eq
  [Fintype V]
  [DecidableEq V]
  {x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)}
  {v : V} :
-- imply
  leeYangAnchor G v ∈ leeYangChoiceSupport G x ↔ x.1 v = true := by
-- proof
  apply StatMech.FrontierA.leeYangAnchor_mem_choiceSupport x v

/--
[leeYangHalf0_mem_choiceSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangHalf0_mem_choiceSupport_eq
  [Fintype V]
  [DecidableEq V]
  {x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)}
  {e : ↑G.edgeFinset} :
-- imply
  leeYangHalf G (leeYangEndpoint0 G e) e ∈ leeYangChoiceSupport G x ↔ (x.2 e).1 = true := by
-- proof
  apply StatMech.FrontierA.leeYangHalf0_mem_choiceSupport x e

/--
[leeYangHalf1_mem_choiceSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangHalf1_mem_choiceSupport_eq
  [Fintype V]
  [DecidableEq V]
  {x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)}
  {e : ↑G.edgeFinset} :
-- imply
  leeYangHalf G (leeYangEndpoint1 G e) e ∈ leeYangChoiceSupport G x ↔ (x.2 e).2 = true := by
-- proof
  apply StatMech.FrontierA.leeYangHalf1_mem_choiceSupport x e

/--
[leeYang_incidence_pair_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYang_incidence_pair_mem_eq
  [Fintype V]
  [DecidableEq V]
  {e : ↑G.edgeFinset}
  {v : V} :
-- imply
  (v, e) ∈ leeYangIncidenceFinset G ↔ v ∈ e.1 := by
-- proof
  apply StatMech.FrontierA.leeYang_incidence_pair_mem e v

/--
[leeYangChoiceSupport_consistent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangChoiceSupport_consistent_iff_eq
  [Fintype V]
  [DecidableEq V]
  {sigma : V → Bool}
  {tau : ↑G.edgeFinset → Bool × Bool} :
-- imply
  LeeYangConsistent G (leeYangIncidenceFinset G).toList (leeYangChoiceSupport G (sigma, tau)) ↔ tau = leeYangTauOf G sigma := by
-- proof
  apply StatMech.FrontierA.leeYangChoiceSupport_consistent_iff sigma tau

/--
[mem_leeYangEraseHalves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma mem_leeYangEraseHalves_eq
  [Fintype V]
  [DecidableEq V]
  {L : List (V × ↑G.edgeFinset)}
  {S : Finset (LeeYangVar G)}
  {k : LeeYangVar G} :
-- imply
  k ∈ leeYangEraseHalves G L S ↔ k ∈ S ∧ ∀ x ∈ L, k ≠ leeYangHalf G x.1 x.2 := by
-- proof
  apply StatMech.FrontierA.mem_leeYangEraseHalves L S k

/--
[leeYangEraseHalves_choiceSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangEraseHalves_choiceSupport_eq
  [Fintype V]
  [DecidableEq V]
  {sigma : V → Bool}
  {tau : ↑G.edgeFinset → Bool × Bool} :
-- imply
  leeYangEraseHalves G (leeYangIncidenceFinset G).toList (leeYangChoiceSupport G (sigma, tau)) = leeYangAnchorSupport G sigma := by
-- proof
  apply StatMech.FrontierA.leeYangEraseHalves_choiceSupport sigma tau

/--
[leeYangContractedProduct_eq_sum_choices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractedProduct_eq_sum_choices_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : LeeYangVar G → ℂ} :
-- imply
  leeYangContractedProduct G beta z = ∑ x : (V → Bool) × (↑G.edgeFinset → Bool × Bool), if x.2 = leeYangTauOf G x.1 then leeYangChoiceWeight G beta x * leeYangMonomial (leeYangAnchorSupport G x.1) z else 0 := by
-- proof
  apply StatMech.FrontierA.leeYangContractedProduct_eq_sum_choices beta z

/--
[leeYangContractedProduct_eq_sum_sigma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractedProduct_eq_sum_sigma_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : LeeYangVar G → ℂ} :
-- imply
  leeYangContractedProduct G beta z = ∑ sigma : V → Bool, leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) * leeYangMonomial (leeYangAnchorSupport G sigma) z := by
-- proof
  apply StatMech.FrontierA.leeYangContractedProduct_eq_sum_sigma beta z

/--
[leeYangMonomial_anchorSupport_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangMonomial_anchorSupport_diagonal_eq
  [Fintype V]
  [DecidableEq V]
  {sigma : V → Bool}
  {q : ℂ} :
-- imply
  leeYangMonomial (leeYangAnchorSupport G sigma) (leeYangDiagonal G q) = q ^ (Finset.univ.filter fun v ↦ sigma v = true).card := by
-- proof
  apply StatMech.FrontierA.leeYangMonomial_anchorSupport_diagonal sigma q

/--
[leeYangChoiceWeight_eq_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangChoiceWeight_eq_ofReal_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {sigma : V → Bool} :
-- imply
  leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) = (leeYangRealChoiceWeight G beta sigma : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangChoiceWeight_eq_ofReal beta sigma

/--
[leeYang_bond_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYang_bond_endpoints_eq
  [Fintype V]
  [DecidableEq V]
  {sigma : ConfigSpace V}
  {e : ↑G.edgeFinset} :
-- imply
  bond sigma e.1 = if sigma (leeYangEndpoint0 G e) = sigma (leeYangEndpoint1 G e) then 1 else -1 := by
-- proof
  apply StatMech.FrontierA.leeYang_bond_endpoints sigma e

/--
[exp_card_mul_leeYangRealChoiceWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma exp_card_mul_leeYangRealChoiceWeight_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {sigma : ConfigSpace V} :
-- imply
  Real.exp (beta * G.edgeFinset.card) * leeYangRealChoiceWeight G beta sigma = zeroFieldInteractionWeight G beta sigma := by
-- proof
  apply StatMech.FrontierA.exp_card_mul_leeYangRealChoiceWeight beta sigma

/--
[eval_leeYangComplexPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma eval_leeYangComplexPolynomial_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {q : ℂ} :
-- imply
  (leeYangComplexPolynomial G beta).eval q = ∑ s : ConfigSpace V, (zeroFieldInteractionWeight G beta s : ℂ) * q ^ minusSpinCount s := by
-- proof
  apply StatMech.FrontierA.eval_leeYangComplexPolynomial beta q

/--
[leeYangContractedProduct_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangContractedProduct_diagonal_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {q : ℂ} :
-- imply
  (Real.exp (beta * G.edgeFinset.card) : ℂ) * leeYangContractedProduct G beta (leeYangDiagonal G q) = (leeYangComplexPolynomial G beta).eval q := by
-- proof
  apply StatMech.FrontierA.leeYangContractedProduct_diagonal beta q

/--
[leeYangComplexPolynomial_ne_zero_in_openUnitDisk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_ne_zero_in_openUnitDisk_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {q : ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hq : ‖q‖ < 1) :
-- imply
  (leeYangComplexPolynomial G beta).eval q ≠ 0 := by
-- proof
  apply StatMech.FrontierA.leeYangComplexPolynomial_ne_zero_in_openUnitDisk hbeta hq

/--
[finiteGraph_hasLeeYangCircle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean)
-/
@[path]
private lemma finiteGraph_hasLeeYangCircle_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  HasLeeYangCircle G beta := by
-- proof
  apply StatMech.FrontierA.finiteGraph_hasLeeYangCircle hbeta


-- created on 2026-10-23
