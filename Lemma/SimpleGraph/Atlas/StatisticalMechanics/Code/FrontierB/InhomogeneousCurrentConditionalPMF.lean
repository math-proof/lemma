import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
open MeasureTheory StatMech StatMech.FrontierB


/--
[summable_inhomogeneousFiniteParityKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma summable_inhomogeneousFiniteParityKernel_eq
  [DecidableEq E]
  {S : Finset E}
-- given
  (lambda : E -> Real)
  (hlambda : forall e : S, 0 < lambda e.1)
  (odd : S -> Bool) :
-- imply
  Summable (inhomogeneousFiniteParityKernel S lambda odd) := by
-- proof
  apply StatMech.FrontierB.summable_inhomogeneousFiniteParityKernel S lambda hlambda odd

/--
[tsum_inhomogeneousFiniteParityKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_inhomogeneousFiniteParityKernel_eq
  [DecidableEq E]
  {S : Finset E}
-- given
  (lambda : E -> Real)
  (hlambda : forall e : S, 0 < lambda e.1)
  (odd : S -> Bool) :
-- imply
  ∑' a : S -> Nat, inhomogeneousFiniteParityKernel S lambda odd a = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_inhomogeneousFiniteParityKernel S lambda hlambda odd

/--
[tsum_ofReal_inhomogeneousFiniteParityKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_ofReal_inhomogeneousFiniteParityKernel_eq
  [DecidableEq E]
  {S : Finset E}
-- given
  (lambda : E -> Real)
  (hlambda : forall e : S, 0 < lambda e.1)
  (odd : S -> Bool) :
-- imply
  ∑' a : S -> Nat, ENNReal.ofReal (inhomogeneousFiniteParityKernel S lambda odd a) = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_ofReal_inhomogeneousFiniteParityKernel S lambda hlambda odd

/--
[inhomogeneousFiniteParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma inhomogeneousFiniteParityPMF_apply_eq
  [DecidableEq E]
  {S : Finset E}
-- given
  (lambda : E -> Real)
  (hlambda : forall e : S, 0 < lambda e.1)
  (odd : S -> Bool)
  (a : S -> Nat) :
-- imply
  inhomogeneousFiniteParityPMF S lambda hlambda odd a = ENNReal.ofReal (inhomogeneousFiniteParityKernel S lambda odd a) := by
-- proof
  apply StatMech.FrontierB.inhomogeneousFiniteParityPMF_apply S lambda hlambda odd a

/--
[inhomogeneousFiniteParityPMF_eq_zero_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma inhomogeneousFiniteParityPMF_eq_zero_of_ne_eq
  [DecidableEq E]
  {S : Finset E}
-- given
  (lambda : E -> Real)
  (hlambda : forall e : S, 0 < lambda e.1)
  (odd : S -> Bool)
  (a : S -> Nat)
  (hodd : odd ≠ currentLocalParity a) :
-- imply
  inhomogeneousFiniteParityPMF S lambda hlambda odd a = 0 := by
-- proof
  apply StatMech.FrontierB.inhomogeneousFiniteParityPMF_eq_zero_of_ne S lambda hlambda odd a hodd

/--
[bind_inhomogeneousFiniteParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma bind_inhomogeneousFiniteParityPMF_apply_eq
  [DecidableEq E]
  {S : Finset E}
-- given
  (lambda : E -> Real)
  (hlambda : forall e : S, 0 < lambda e.1)
  (p : PMF (S -> Bool))
  (a : S -> Nat) :
-- imply
  p.bind (inhomogeneousFiniteParityPMF S lambda hlambda) a = p (currentLocalParity a) * inhomogeneousFiniteParityPMF S lambda hlambda (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.bind_inhomogeneousFiniteParityPMF_apply S lambda hlambda p a

/--
[summable_inhomogeneousParityCurrentKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma summable_inhomogeneousParityCurrentKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : Finset (Sym2 V)}
-- given
  (lambda : Sym2 V -> Real)
  (hlambda : forall e : G.edgeFinset, 0 < lambda e.1) :
-- imply
  Summable (inhomogeneousParityCurrentKernel G lambda H) := by
-- proof
  apply StatMech.FrontierB.summable_inhomogeneousParityCurrentKernel G lambda hlambda H

/--
[tsum_inhomogeneousParityCurrentKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_inhomogeneousParityCurrentKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : Finset (Sym2 V)}
-- given
  (lambda : Sym2 V -> Real)
  (hlambda : forall e : G.edgeFinset, 0 < lambda e.1) :
-- imply
  ∑' m : EdgeCurrent G, inhomogeneousParityCurrentKernel G lambda H m = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_inhomogeneousParityCurrentKernel G lambda hlambda H

/--
[tsum_ofReal_inhomogeneousParityCurrentKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma tsum_ofReal_inhomogeneousParityCurrentKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : Finset (Sym2 V)}
-- given
  (lambda : Sym2 V -> Real)
  (hlambda : forall e : G.edgeFinset, 0 < lambda e.1) :
-- imply
  ∑' m : EdgeCurrent G, ENNReal.ofReal (inhomogeneousParityCurrentKernel G lambda H m) = 1 := by
-- proof
  apply StatMech.FrontierB.tsum_ofReal_inhomogeneousParityCurrentKernel G lambda hlambda H

/--
[inhomogeneousParityCurrentPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma inhomogeneousParityCurrentPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : Finset (Sym2 V)}
  {m : EdgeCurrent G}
-- given
  (lambda : Sym2 V -> Real)
  (hlambda : forall e : G.edgeFinset, 0 < lambda e.1) :
-- imply
  inhomogeneousParityCurrentPMF G lambda hlambda H m = ENNReal.ofReal (inhomogeneousParityCurrentKernel G lambda H m) := by
-- proof
  apply StatMech.FrontierB.inhomogeneousParityCurrentPMF_apply G lambda hlambda H m

/--
[inhomogeneousParityCurrentKernel_eq_zero_of_support_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma inhomogeneousParityCurrentKernel_eq_zero_of_support_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : Finset (Sym2 V)}
  {m : EdgeCurrent G}
-- given
  (lambda : Sym2 V -> Real)
  (hH : H ⊆ G.edgeFinset)
  (hm : currentParitySupport G m ≠ H) :
-- imply
  inhomogeneousParityCurrentKernel G lambda H m = 0 := by
-- proof
  apply StatMech.FrontierB.inhomogeneousParityCurrentKernel_eq_zero_of_support_ne G lambda H hH m hm

/--
[weight_eq_inhomogeneousParityFiberMass_mul_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma weight_eq_inhomogeneousParityFiberMass_mul_kernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {H : Finset (Sym2 V)}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (J : Sym2 V -> Real)
  (hJ : forall e : G.edgeFinset, 0 < J e.1)
  (hH : H ⊆ G.edgeFinset)
  (hm : currentParitySupport G m = H) :
-- imply
  weight G beta J (ofEdgeFun G m) = inhomogeneousParityFiberMass G (fun e => beta * J e) H * inhomogeneousParityCurrentKernel G (fun e => beta * J e) H m := by
-- proof
  apply StatMech.FrontierB.weight_eq_inhomogeneousParityFiberMass_mul_kernel G beta hbeta J hJ H hH m hm

/--
[fixedParity_weight_tsum_inhomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean)
-/
@[path]
private lemma fixedParity_weight_tsum_inhomogeneous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (J : Sym2 V -> Real)
  (hJ : forall e : G.edgeFinset, 0 < J e.1)
  (hH : H ⊆ G.edgeFinset) :
-- imply
  (∑' m : EdgeCurrent G, if currentParitySupport G m = H then weight G beta J (ofEdgeFun G m) else 0) = inhomogeneousParityFiberMass G (fun e => beta * J e) H := by
-- proof
  apply StatMech.FrontierB.fixedParity_weight_tsum_inhomogeneous G beta hbeta J hJ H hH


-- created on 2026-10-23
