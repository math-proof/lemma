import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CutResummation.Part3
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[shb_cutJoin_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_cutJoin_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred P]
  (ab)
  {e : G.edgeFinset}
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  shb_cutJoin G P ab e = if h : P e then ab.1 ⟨e, h⟩ else ab.2 ⟨e, h⟩ := by
-- proof
  apply StatMech.Sharpness.shb_cutJoin_apply G P e

/--
[shb_cutLeft_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_cutLeft_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred P]
  (a)
  {e : G.edgeFinset}
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  shb_cutLeft G P a e = if h : P e then a ⟨e, h⟩ else 0 := by
-- proof
  apply StatMech.Sharpness.shb_cutLeft_apply G P e

/--
[shb_cutRight_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_cutRight_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred P]
  (b)
  {e : G.edgeFinset}
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  shb_cutRight G P b e = if h : P e then 0 else b ⟨e, h⟩ := by
-- proof
  apply StatMech.Sharpness.shb_cutRight_apply G P e

/--
[shb_ofEdgeFun_cutJoin_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_ofEdgeFun_cutJoin_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred P]
  (a b)
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  (fun e => ofEdgeFun G (shb_cutLeft G P a) e + ofEdgeFun G (shb_cutRight G P b) e) = ofEdgeFun G (shb_cutJoin G P (a, b)) := by
-- proof
  apply StatMech.Sharpness.shb_ofEdgeFun_cutJoin_add G P

/--
[shb_weight_cutJoin_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_weight_cutJoin_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred P]
  (a b)
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  weight G β J (ofEdgeFun G (shb_cutJoin G P (a, b))) = weight G β J (ofEdgeFun G (shb_cutLeft G P a)) * weight G β J (ofEdgeFun G (shb_cutRight G P b)) := by
-- proof
  apply StatMech.Sharpness.shb_weight_cutJoin_split G β J P

/--
[shb_cutLeft_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_cutLeft_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred P]
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  Function.Injective (shb_cutLeft G P) := by
-- proof
  apply StatMech.Sharpness.shb_cutLeft_injective G P

/--
[shb_cutRight_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_cutRight_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred P]
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  Function.Injective (shb_cutRight G P) := by
-- proof
  apply StatMech.Sharpness.shb_cutRight_injective G P

/--
[shb_cutJoinWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_cutJoinWeight_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred P]
  (ab)
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  shb_cutJoinWeight G β J P ab = shb_cutLeftWeight G β J P ab.1 * shb_cutRightWeight G β J P ab.2 := by
-- proof
  apply StatMech.Sharpness.shb_cutJoinWeight_factor G β J P

/--
[shb_summable_weight_cutLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_summable_weight_cutLeft_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred P]
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  Summable (fun a : {e : G.edgeFinset // P e} → ℕ => shb_cutLeftWeight G β J P a) := by
-- proof
  apply StatMech.Sharpness.shb_summable_weight_cutLeft G β J P

/--
[shb_summable_weight_cutRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_summable_weight_cutRight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred P]
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  Summable (fun b : {e : G.edgeFinset // ¬ P e} → ℕ => shb_cutRightWeight G β J P b) := by
-- proof
  apply StatMech.Sharpness.shb_summable_weight_cutRight G β J P

/--
[shb_tsum_prod_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_tsum_prod_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : A → ℝ}
  {g : B → ℝ}
-- given
  (hf : Summable f)
  (hg : Summable g) :
-- imply
  (∑' ab : A × B, f ab.1 * g ab.2) = (∑' a, f a) * ∑' b, g b := by
-- proof
  apply StatMech.Sharpness.shb_tsum_prod_factor G f g hf hg

/--
[shb_fullWeightMass_eq_cutJoinMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_fullWeightMass_eq_cutJoinMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred P]
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  shb_fullWeightMass G β J = shb_cutJoinMass G β J P := by
-- proof
  apply StatMech.Sharpness.shb_fullWeightMass_eq_cutJoinMass G β J P

/--
[shb_cutJoinMass_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_cutJoinMass_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred P]
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  shb_cutJoinMass G β J P = shb_cutLeftMass G β J P * shb_cutRightMass G β J P := by
-- proof
  apply StatMech.Sharpness.shb_cutJoinMass_factor G β J P

/--
[shb_tsum_weight_cut_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean)
-/
@[path]
private lemma shb_tsum_weight_cut_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred P]
-- given
  (P : G.edgeFinset → Prop) :
-- imply
  shb_fullWeightMass G β J = shb_cutLeftMass G β J P * shb_cutRightMass G β J P := by
-- proof
  apply StatMech.Sharpness.shb_tsum_weight_cut_factor G β J P


-- created on 2026-10-23
