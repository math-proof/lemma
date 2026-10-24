import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.HcovAssembly
open Finset BigOperators SimpleGraph StatMech StatMech.Sharpness StatMech.Sharpness.HcovAssembly


/--
[hca_gap_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_gap_disconn_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {m : ↥H.edgeFinset → ℕ}
  {A : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  hca_gap H m A u v = (if ¬ connK (endsM H m) univ u v then (1 : ℝ) else 0) * hca_gap H m A u v := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_gap_disconn H m A huv

/--
[hca_gap_mul_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_gap_mul_weight_eq_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
  {m : ↥H.edgeFinset → ℕ} :
-- imply
  hca_gap H m A u v * weight H β J (ofEdgeFun H m) = (∑ S : Finset (Copy H m), (if RandomCurrent.sources (endsM H m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM H m) (univ \ S) = (∅ : Finset V) then 1 else 0)) * weight H β J (ofEdgeFun H m) - (∑ S : Finset (Copy H m), (if RandomCurrent.sources (endsM H m) S = A ∆ {u, v} then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM H m) (univ \ S) = ({u, v} : Finset V) then 1 else 0)) * weight H β J (ofEdgeFun H m) := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_gap_mul_weight_eq H β J A u v m

/--
[hca_summable_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_summable_gap_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V} :
-- imply
  Summable (fun m : ↥H.edgeFinset → ℕ => hca_gap H m A u v * weight H β J (ofEdgeFun H m)) := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_summable_gap H β J A u v

/--
[hca_summable_pairSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_summable_pairSum_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (P : (↥H.edgeFinset → ℕ) → Prop) :
-- imply
  Summable (fun m : ↥H.edgeFinset → ℕ => (if P m then (1 : ℝ) else 0) * hca_gap H m A u v * weight H β J (ofEdgeFun H m)) := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_summable_pairSum H β J A u v P

/--
[hca_pairSum_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_pairSum_add_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (P₁ P₂ : (↥H.edgeFinset → ℕ) → Prop)
  (hdisj : ∀ m, ¬ (P₁ m ∧ P₂ m)) :
-- imply
  hca_pairSum H β J A u v (fun m => P₁ m ∨ P₂ m) = hca_pairSum H β J A u v P₁ + hca_pairSum H β J A u v P₂ := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_pairSum_add H β J A u v P₁ P₂ hdisj

/--
[hca_pairSum_disconn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_pairSum_disconn_eq_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  hca_pairSum H β J A u v (fun m => ¬ connK (endsM H m) univ u v) = sourcePairDisconnSum H β J A ∅ u v := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_pairSum_disconn_eq H β J A huv

/--
[hca_gap_srcGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_gap_srcGate_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {m : ↥H.edgeFinset → ℕ}
  {A : Finset V}
  {u v : V} :
-- imply
  hca_gap H m A u v = (if RandomCurrent.sources (endsM H m) univ = A then (1 : ℝ) else 0) * hca_gap H m A u v := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_gap_srcGate H m A u v

/--
[hca_pairSum_disconn_conj_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_pairSum_disconn_conj_eq_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  hca_pairSum H β J A u v (fun m => RandomCurrent.sources (endsM H m) univ = A ∧ ¬ connK (endsM H m) univ u v) = sourcePairDisconnSum H β J A ∅ u v := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_pairSum_disconn_conj_eq H β J A huv

/--
[hca_sourcePairDisconn_deltaRewrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_sourcePairDisconn_deltaRewrite_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  sourcePairDisconnSum H β J ({o, x, y, g} : Finset V) ∅ o g = hca_pairSum H β J ({o, x, y, g} : Finset V) o g (fun m => (RandomCurrent.sources (endsM H m) univ = {o, x, y, g} ∧ ¬ connK (endsM H m) univ o g) ∧ (connK (endsM H m) univ o x ∧ connK (endsM H m) univ y g)) + hca_pairSum H β J ({o, x, y, g} : Finset V) o g (fun m => (RandomCurrent.sources (endsM H m) univ = {o, x, y, g} ∧ ¬ connK (endsM H m) univ o g) ∧ (connK (endsM H m) univ o y ∧ connK (endsM H m) univ x g)) := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_sourcePairDisconn_deltaRewrite H β J hox hoy hog hxy hxg hyg

/--
[hcaBondSource_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hcaBondSource_mk_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V} :
-- imply
  hcaBondSource o s(x, y) = insert none ((({o} : Finset V) ∆ {x, y}).map someEmb) := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hcaBondSource_mk H G o x y

/--
[hca_bond_covariance_sourcePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_bond_covariance_sourcePair_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hxy : x ≠ y)
  (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2 * (isingExpectation G β h (spinProd (({o} : Finset V) ∆ {x, y})) - isingExpectation G β h (spinProd ({x, y} : Finset V)) * isingExpectation G β h (spinProd ({o} : Finset V))) = hcaBondDelta G β h o s(x, y) := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_bond_covariance_sourcePair H G β h o x y hxy hZne

/--
[hca_field_covariance_sourcePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_field_covariance_sourcePair_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o z : V}
-- given
  (β h : ℝ)
  (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2 * (isingExpectation G β h (spinProd (({o} : Finset V) ∆ {z})) - isingExpectation G β h (spinProd ({z} : Finset V)) * isingExpectation G β h (spinProd ({o} : Finset V))) = hcaFieldDelta G β h o z := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_field_covariance_sourcePair H G β h o z hZne

/--
[hca_bond_covariance_eq_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_bond_covariance_eq_delta_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {e : Sym2 V}
-- given
  (β h : ℝ)
  (he : e ∈ G.edgeFinset)
  (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2 * (isingExpectation G β h (fun s => Ising.spin s o * Ising.bond s e) - isingExpectation G β h (fun s => Ising.bond s e) * isingExpectation G β h (fun s => Ising.spin s o)) = hcaBondDelta G β h o e := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_bond_covariance_eq_delta H G β h o e he hZne

/--
[hca_field_covariance_eq_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_field_covariance_eq_delta_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o z : V}
-- given
  (β h : ℝ)
  (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2 * (isingExpectation G β h (fun s => Ising.spin s o * Ising.spin s z) - isingExpectation G β h (fun s => Ising.spin s z) * isingExpectation G β h (fun s => Ising.spin s o)) = hcaFieldDelta G β h o z := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_field_covariance_eq_delta H G β h o z hZne

/--
[hca_deriv_magnetization_eq_currentDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_deriv_magnetization_eq_currentDelta_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => isingExpectation G β h (fun s => Ising.spin s o)) ((1 / (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2) * ((∑ e ∈ G.edgeFinset, hcaBondDelta G β h o e) + h * ∑ z, hcaFieldDelta G β h o z)) β := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_deriv_magnetization_eq_currentDelta H G β h o

/--
[hca_odd_bond_covariance_sourcePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_odd_bond_covariance_sourcePair_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2 * (isingExpectation G β h (spinProd ({o, x, y} : Finset V)) - isingExpectation G β h (spinProd ({x, y} : Finset V)) * isingExpectation G β h (spinProd ({o} : Finset V))) = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, some x, some y, none} : Finset (Option V)) ∅ (some o) none := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_odd_bond_covariance_sourcePair H G β h hox hoy hxy hZne

/--
[hca_odd_bond_covariance_deltaRewrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_odd_bond_covariance_deltaRewrite_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2 * (isingExpectation G β h (spinProd ({o, x, y} : Finset V)) - isingExpectation G β h (spinProd ({x, y} : Finset V)) * isingExpectation G β h (spinProd ({o} : Finset V))) = hca_pairSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, some x, some y, none} : Finset (Option V)) (some o) none (fun m => (RandomCurrent.sources (endsM (withGhost G) m) univ = {some o, some x, some y, none} ∧ ¬ connK (endsM (withGhost G) m) univ (some o) none) ∧ (connK (endsM (withGhost G) m) univ (some o) (some x) ∧ connK (endsM (withGhost G) m) univ (some y) none)) + hca_pairSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, some x, some y, none} : Finset (Option V)) (some o) none (fun m => (RandomCurrent.sources (endsM (withGhost G) m) univ = {some o, some x, some y, none} ∧ ¬ connK (endsM (withGhost G) m) univ (some o) none) ∧ (connK (endsM (withGhost G) m) univ (some o) (some y) ∧ connK (endsM (withGhost G) m) univ (some x) none)) := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_odd_bond_covariance_deltaRewrite H G β h hox hoy hxy hZne

/--
[hca_covariance_deltaRewrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_covariance_deltaRewrite_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y g : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2 * (isingExpectation G β h (spinProd ({o, x, y, g} : Finset V)) - isingExpectation G β h (spinProd ({x, y} : Finset V)) * isingExpectation G β h (spinProd ({o, g} : Finset V))) = hca_pairSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, some x, some y, some g} : Finset (Option V)) (some o) (some g) (fun m => (RandomCurrent.sources (endsM (withGhost G) m) univ = {some o, some x, some y, some g} ∧ ¬ connK (endsM (withGhost G) m) univ (some o) (some g)) ∧ (connK (endsM (withGhost G) m) univ (some o) (some x) ∧ connK (endsM (withGhost G) m) univ (some y) (some g))) + hca_pairSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, some x, some y, some g} : Finset (Option V)) (some o) (some g) (fun m => (RandomCurrent.sources (endsM (withGhost G) m) univ = {some o, some x, some y, some g} ∧ ¬ connK (endsM (withGhost G) m) univ (some o) (some g)) ∧ (connK (endsM (withGhost G) m) univ (some o) (some y) ∧ connK (endsM (withGhost G) m) univ (some x) (some g))) := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_covariance_deltaRewrite H G β h hox hoy hog hxy hxg hyg hZne

/--
[hca_pairSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_pairSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJnn : ∀ e, 0 ≤ J e)
  (huv : u ≠ v)
  (P : (↥H.edgeFinset → ℕ) → Prop)
  (hP : ∀ m, P m → ¬ connK (endsM H m) univ u v) :
-- imply
  0 ≤ hca_pairSum H β J A u v P := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_pairSum_nonneg H G β J hβ hJnn A huv P hP

/--
[hcaBondDelta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hcaBondDelta_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {e : Sym2 V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ hcaBondDelta G β h o e := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hcaBondDelta_nonneg H G β h hβ hh o e

/--
[hcaFieldDelta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hcaFieldDelta_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o z : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ hcaFieldDelta G β h o z := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hcaFieldDelta_nonneg H G β h hβ hh o z

/--
[hca_currentDelta_derivative_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_currentDelta_derivative_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ (1 / (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2) * ((∑ e ∈ G.edgeFinset, hcaBondDelta G β h o e) + h * ∑ z, hcaFieldDelta G β h o z) := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_currentDelta_derivative_nonneg H G β h hβ hh o

/--
[hca_sourcePairDisconn_deltaRewrite_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean)
-/
@[path]
private lemma hca_sourcePairDisconn_deltaRewrite_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  sourcePairDisconnSum (⊤ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ({0, 1, 2, 3} : Finset (Fin 4)) ∅ 0 3 = hca_pairSum (⊤ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ({0, 1, 2, 3} : Finset (Fin 4)) 0 3 (fun m => (RandomCurrent.sources (endsM (⊤ : SimpleGraph (Fin 4)) m) univ = {0, 1, 2, 3} ∧ ¬ connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 0 3) ∧ (connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 0 1 ∧ connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 2 3)) + hca_pairSum (⊤ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ({0, 1, 2, 3} : Finset (Fin 4)) 0 3 (fun m => (RandomCurrent.sources (endsM (⊤ : SimpleGraph (Fin 4)) m) univ = {0, 1, 2, 3} ∧ ¬ connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 0 3) ∧ (connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 0 2 ∧ connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 1 3)) := by
-- proof
  apply StatMech.Sharpness.HcovAssembly.hca_sourcePairDisconn_deltaRewrite_nonvacuous H G


-- created on 2026-10-23
