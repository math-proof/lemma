import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
open StatMech StatMech.Universality


/--
[hexW2_halfWt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean)
-/
@[path]
private lemma hexW2_halfWt_nonneg_eq
  {x : ℝ}
  {b : HexW2Half}
-- given
  (hx : 0 ≤ x) :
-- imply
  0 ≤ hexW2_halfWt x b := by
-- proof
  apply StatMech.Universality.hexW2_halfWt_nonneg x hx b

/--
[hexW2_split_fst_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean)
-/
@[path]
private lemma hexW2_split_fst_wt_eq
  {a : ℂ}
  {x : ℝ}
  {d : {ts // memD ts}}
-- given
  (h0 : ℤ)
  (memD : List ℤ → Prop) :
-- imply
  hexW2_halfWt x (hexW2_split a h0 memD d).1 = hexSAWwt a h0 x (d.1.take (hexW2_cutPos h0 d.1)) := by
-- proof
  apply StatMech.Universality.hexW2_split_fst_wt a h0 x memD d

/--
[hexW2_split_snd_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean)
-/
@[path]
private lemma hexW2_split_snd_wt_eq
  {a : ℂ}
  {x : ℝ}
  {d : {ts // memD ts}}
-- given
  (h0 : ℤ)
  (memD : List ℤ → Prop) :
-- imply
  hexW2_halfWt x (hexW2_split a h0 memD d).2 = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1)) (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1)) := by
-- proof
  apply StatMech.Universality.hexW2_split_snd_wt a h0 x memD d

/--
[hexW2_split_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean)
-/
@[path]
private lemma hexW2_split_injective_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (memD : List ℤ → Prop) :
-- imply
  Function.Injective (hexW2_split a h0 memD) := by
-- proof
  apply StatMech.Universality.hexW2_split_injective a h0 memD

/--
[hexW2_halves_displacement_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean)
-/
@[path]
private lemma hexW2_halves_displacement_split_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_stepReSum h0 ts = hexInfra_stepReSum (hexW2_lowerHalf a h0 ts).head (hexW2_lowerHalf a h0 ts).turns + hexInfra_stepReSum (hexW2_upperHalf a h0 ts).head (hexW2_upperHalf a h0 ts).turns := by
-- proof
  apply StatMech.Universality.hexW2_halves_displacement_split a h0 ts

/--
[hexW2_singleRight_split_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean)
-/
@[path]
private lemma hexW2_singleRight_split_wt_eq
  {a : ℂ}
  {x : ℝ} :
-- imply
  hexW2_halfWt x (hexW2_split a 0 hexW2_singleRight_memD hexW2_singleRight_elt).1 = hexSAWwt a 0 x ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)])) ∧ hexW2_halfWt x (hexW2_split a 0 hexW2_singleRight_memD hexW2_singleRight_elt).2 = hexSAWwt (hexDropMid a 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)])) (0 + ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)])).sum) x ([(-1 : ℤ)].drop (hexW2_cutPos 0 [(-1 : ℤ)])) := by
-- proof
  apply StatMech.Universality.hexW2_singleRight_split_wt a x

/--
[hexW2_singleRight_split_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean)
-/
@[path]
private lemma hexW2_singleRight_split_injective_eq
  {a : ℂ} :
-- imply
  Function.Injective (hexW2_split a 0 hexW2_singleRight_memD) := by
-- proof
  apply StatMech.Universality.hexW2_singleRight_split_injective a


-- created on 2026-10-23
