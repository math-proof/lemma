import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part5
open StatMech StatMech.FrontierB


/--
[nonnegativeParityEdgeKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma nonnegativeParityEdgeKernel_nonneg_eq
  {lambda : ℝ}
  {odd : Bool}
  {k : ℕ}
-- given
  (hlambda : 0 ≤ lambda) :
-- imply
  0 ≤ nonnegativeParityEdgeKernel lambda odd k := by
-- proof
  apply StatMech.FrontierB.nonnegativeParityEdgeKernel_nonneg hlambda odd k

/--
[summable_nonnegativeParityEdgeKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma summable_nonnegativeParityEdgeKernel_eq
  {lambda : ℝ}
  {odd : Bool}
-- given
  (_hlambda : 0 ≤ lambda) :
-- imply
  Summable (nonnegativeParityEdgeKernel lambda odd) := by
-- proof
  apply StatMech.FrontierB.summable_nonnegativeParityEdgeKernel _hlambda odd

/--
[tsum_nonnegativeParityEdgeKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_nonnegativeParityEdgeKernel_eq
  {lambda : ℝ}
  {odd : Bool}
-- given
  (hlambda : 0 ≤ lambda) :
-- imply
  ∑' k : ℕ, nonnegativeParityEdgeKernel lambda odd k = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_nonnegativeParityEdgeKernel hlambda odd

/--
[nonnegativeParityEdgeKernel_eq_zero_of_parity_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma nonnegativeParityEdgeKernel_eq_zero_of_parity_ne_eq
  {lambda : ℝ}
  {odd : Bool}
  {k : ℕ}
-- given
  (hpar : ¬(if odd then Odd k else Even k)) :
-- imply
  nonnegativeParityEdgeKernel lambda odd k = 0 := by
-- proof
  apply StatMech.FrontierB.nonnegativeParityEdgeKernel_eq_zero_of_parity_ne lambda odd k hpar

/--
[parityFiberMass_mul_nonnegativeParityEdgeKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma parityFiberMass_mul_nonnegativeParityEdgeKernel_eq
  {lambda : ℝ}
  {odd : Bool}
  {k : ℕ}
-- given
  (hlambda : 0 ≤ lambda)
  (hpar : if odd then Odd k else Even k) :
-- imply
  (if odd then Real.sinh lambda else Real.cosh lambda) * nonnegativeParityEdgeKernel lambda odd k = lambda ^ k / k.factorial := by
-- proof
  apply StatMech.FrontierB.parityFiberMass_mul_nonnegativeParityEdgeKernel hlambda odd k hpar

/--
[summable_nonnegativeFiniteParityKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma summable_nonnegativeFiniteParityKernel_eq
  [DecidableEq E]
  {S : Finset E}
  {lambda : E → ℝ}
  {odd : ↑S → Bool}
-- given
  (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) :
-- imply
  Summable (nonnegativeFiniteParityKernel S lambda odd) := by
-- proof
  apply StatMech.FrontierB.summable_nonnegativeFiniteParityKernel S lambda hlambda odd

/--
[tsum_nonnegativeFiniteParityKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_nonnegativeFiniteParityKernel_eq
  [DecidableEq E]
  {S : Finset E}
  {lambda : E → ℝ}
  {odd : ↑S → Bool}
-- given
  (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) :
-- imply
  ∑' a : ↑S → ℕ, nonnegativeFiniteParityKernel S lambda odd a = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_nonnegativeFiniteParityKernel S lambda hlambda odd

/--
[tsum_ofReal_nonnegativeFiniteParityKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_ofReal_nonnegativeFiniteParityKernel_eq
  [DecidableEq E]
  {S : Finset E}
  {lambda : E → ℝ}
  {odd : ↑S → Bool}
-- given
  (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) :
-- imply
  ∑' a : ↑S → ℕ, ENNReal.ofReal (nonnegativeFiniteParityKernel S lambda odd a) = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_ofReal_nonnegativeFiniteParityKernel S lambda hlambda odd

/--
[nonnegativeFiniteParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma nonnegativeFiniteParityPMF_apply_eq
  [DecidableEq E]
  {S : Finset E}
  {lambda : E → ℝ}
  {odd : ↑S → Bool}
  {a : ↑S → ℕ}
-- given
  (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) :
-- imply
  nonnegativeFiniteParityPMF S lambda hlambda odd a = ENNReal.ofReal (nonnegativeFiniteParityKernel S lambda odd a) := by
-- proof
  apply StatMech.FrontierB.nonnegativeFiniteParityPMF_apply S lambda hlambda odd a

/--
[nonnegativeFiniteParityPMF_eq_zero_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma nonnegativeFiniteParityPMF_eq_zero_of_ne_eq
  [DecidableEq E]
  {S : Finset E}
  {lambda : E → ℝ}
  {odd : ↑S → Bool}
  {a : ↑S → Nat}
-- given
  (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1)
  (hodd : odd ≠ currentLocalParity a) :
-- imply
  nonnegativeFiniteParityPMF S lambda hlambda odd a = 0 := by
-- proof
  apply StatMech.FrontierB.nonnegativeFiniteParityPMF_eq_zero_of_ne S lambda hlambda odd a hodd

/--
[bind_nonnegativeFiniteParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma bind_nonnegativeFiniteParityPMF_apply_eq
  [DecidableEq E]
  {S : Finset E}
  {lambda : E → ℝ}
  {p : PMF (↑S → Bool)}
  {a : ↑S → Nat}
-- given
  (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) :
-- imply
  p.bind (nonnegativeFiniteParityPMF S lambda hlambda) a = p (currentLocalParity a) * nonnegativeFiniteParityPMF S lambda hlambda (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.bind_nonnegativeFiniteParityPMF_apply S lambda hlambda p a

/--
[inhomogeneousParityFiberMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma inhomogeneousParityFiberMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1) :
-- imply
  0 ≤ inhomogeneousParityFiberMass G lambda H := by
-- proof
  apply StatMech.FrontierB.inhomogeneousParityFiberMass_nonneg G lambda hlambda H

/--
[summable_nonnegativeParityCurrentKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma summable_nonnegativeParityCurrentKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1) :
-- imply
  Summable (nonnegativeParityCurrentKernel G lambda H) := by
-- proof
  apply StatMech.FrontierB.summable_nonnegativeParityCurrentKernel G lambda hlambda H

/--
[tsum_nonnegativeParityCurrentKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_nonnegativeParityCurrentKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1) :
-- imply
  ∑' m : EdgeCurrent G, nonnegativeParityCurrentKernel G lambda H m = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_nonnegativeParityCurrentKernel G lambda hlambda H

/--
[nonnegativeParityCurrentKernel_eq_zero_of_support_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma nonnegativeParityCurrentKernel_eq_zero_of_support_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
  {m : EdgeCurrent G}
-- given
  (hH : H ⊆ G.edgeFinset)
  (hm : currentParitySupport G m ≠ H) :
-- imply
  nonnegativeParityCurrentKernel G lambda H m = 0 := by
-- proof
  apply StatMech.FrontierB.nonnegativeParityCurrentKernel_eq_zero_of_support_ne G lambda H hH m hm

/--
[weight_eq_nonnegativeParityFiberMass_mul_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma weight_eq_nonnegativeParityFiberMass_mul_kernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e : G.edgeFinset, 0 ≤ J e.1)
  (hH : H ⊆ G.edgeFinset)
  (hm : currentParitySupport G m = H) :
-- imply
  weight G beta J (ofEdgeFun G m) = inhomogeneousParityFiberMass G (fun e => beta * J e) H * nonnegativeParityCurrentKernel G (fun e => beta * J e) H m := by
-- proof
  apply StatMech.FrontierB.weight_eq_nonnegativeParityFiberMass_mul_kernel G beta hbeta J hJ H hH m hm

/--
[summable_fixedParity_weight_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma summable_fixedParity_weight_nonnegative_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e : G.edgeFinset, 0 ≤ J e.1)
  (hH : H ⊆ G.edgeFinset) :
-- imply
  Summable (fun m : EdgeCurrent G => if currentParitySupport G m = H then weight G beta J (ofEdgeFun G m) else 0) := by
-- proof
  apply StatMech.FrontierB.summable_fixedParity_weight_nonnegative G beta hbeta J hJ H hH

/--
[fixedParity_weight_tsum_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma fixedParity_weight_tsum_nonnegative_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e : G.edgeFinset, 0 ≤ J e.1)
  (hH : H ⊆ G.edgeFinset) :
-- imply
  (∑' m : EdgeCurrent G, if currentParitySupport G m = H then weight G beta J (ofEdgeFun G m) else 0) = inhomogeneousParityFiberMass G (fun e => beta * J e) H := by
-- proof
  apply StatMech.FrontierB.fixedParity_weight_tsum_nonnegative G beta hbeta J hJ H hH

/--
[sourcelessNonnegativeParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma sourcelessNonnegativeParityPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  sourcelessNonnegativeParityPMF G beta J hbeta.le hJ H = if _hH : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then ENNReal.ofReal (inhomogeneousParityFiberMass G (fun e => beta * J e) H) * (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ else 0 := by
-- proof
  apply StatMech.FrontierB.sourcelessNonnegativeParityPMF_apply G beta hbeta J hJ H

/--
[sourcelessCurrentPMF_apply_eq_nonnegativeParity_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma sourcelessCurrentPMF_apply_eq_nonnegativeParity_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  sourcelessCurrentPMF G beta J hbeta.le hJ m = sourcelessNonnegativeParityPMF G beta J hbeta.le hJ (currentParitySupport G m) * nonnegativeFiniteParityPMF G.edgeFinset (fun e => beta * J e) (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1)) (fun e : G.edgeFinset => e.1 ∈ currentParitySupport G m) m := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentPMF_apply_eq_nonnegativeParity_factor G beta hbeta J hJ m

/--
[sourcelessCurrentPMF_eq_nonnegativeParity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma sourcelessCurrentPMF_eq_nonnegativeParity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  sourcelessCurrentPMF G beta J hbeta.le hJ = (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).bind (fun H => nonnegativeFiniteParityPMF G.edgeFinset (fun e => beta * J e) (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1)) (fun e : G.edgeFinset => e.1 ∈ H)) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentPMF_eq_nonnegativeParity_bind G beta hbeta J hJ

/--
[sourcelessCurrentPMF_map_eq_nonnegativeParity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean)
-/
@[path]
private lemma sourcelessCurrentPMF_map_eq_nonnegativeParity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {f : EdgeCurrent G → A}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  PMF.map f (sourcelessCurrentPMF G beta J hbeta.le hJ) = (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).bind (fun H => PMF.map f (nonnegativeFiniteParityPMF G.edgeFinset (fun e => beta * J e) (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1)) (fun e : G.edgeFinset => e.1 ∈ H))) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentPMF_map_eq_nonnegativeParity_bind G beta hbeta J hJ f


-- created on 2026-10-23
