import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.SLE.CardyCLE
open Complex Filter Topology StatMech StatMech.SLE


/--
[discConformalRadius_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma discConformalRadius_apply_eq
  {r : ℝ} :
-- imply
  discConformalRadius r = r := by
-- proof
  apply StatMech.SLE.discConformalRadius_apply r

/--
[discRiemannMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma discRiemannMap_apply_eq
  {z : ℂ}
  {r : ℝ}
  {w : ℂ} :
-- imply
  discRiemannMap z r w = z + (r : ℂ) * w := by
-- proof
  apply StatMech.SLE.discRiemannMap_apply z r w

/--
[discRiemannMap_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma discRiemannMap_zero_eq
  {z : ℂ}
  {r : ℝ} :
-- imply
  discRiemannMap z r 0 = z := by
-- proof
  apply StatMech.SLE.discRiemannMap_zero z r

/--
[hasDerivAt_discRiemannMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma hasDerivAt_discRiemannMap_eq
  {z : ℂ}
  {r : ℝ} :
-- imply
  HasDerivAt (discRiemannMap z r) (r : ℂ) 0 := by
-- proof
  apply StatMech.SLE.hasDerivAt_discRiemannMap z r

/--
[hasConformalRadius_disc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma hasConformalRadius_disc_eq
  {z : ℂ}
  {r : ℝ}
-- given
  (hr : 0 < r) :
-- imply
  HasConformalRadius z (discRiemannMap z r) r := by
-- proof
  apply StatMech.SLE.hasConformalRadius_disc z hr

/--
[HasConformalRadius.pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma pos_eq
  {z : ℂ}
  {φ : ℂ → ℂ}
  {r : ℝ}
-- given
  (h : HasConformalRadius z φ r) :
-- imply
  0 < r := by
-- proof
  apply StatMech.SLE.HasConformalRadius.pos h

/--
[HasConformalRadius.map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma map_zero_eq
  {z : ℂ}
  {φ : ℂ → ℂ}
  {r : ℝ}
-- given
  (h : HasConformalRadius z φ r) :
-- imply
  φ 0 = z := by
-- proof
  apply StatMech.SLE.HasConformalRadius.map_zero h

/--
[HasConformalRadius.unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma unique_eq
  {z : ℂ}
  {φ : ℂ → ℂ}
  {r₁ r₂ : ℝ}
-- given
  (h₁ : HasConformalRadius z φ r₁)
  (h₂ : HasConformalRadius z φ r₂) :
-- imply
  r₁ = r₂ := by
-- proof
  apply StatMech.SLE.HasConformalRadius.unique h₁ h₂

/--
[discConformalRadius_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma discConformalRadius_strictMono_eq :
-- imply
  StrictMono discConformalRadius := by
-- proof
  apply StatMech.SLE.discConformalRadius_strictMono

/--
[discConformalRadius_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma discConformalRadius_mono_eq :
-- imply
  Monotone discConformalRadius := by
-- proof
  apply StatMech.SLE.discConformalRadius_mono

/--
[discConformalRadius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma discConformalRadius_pos_eq
  {r : ℝ}
-- given
  (hr : 0 < r) :
-- imply
  0 < discConformalRadius r := by
-- proof
  apply StatMech.SLE.discConformalRadius_pos hr

/--
[slePhase_of_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_of_le_four_eq
  {κ : ℝ}
-- given
  (h : κ ≤ 4) :
-- imply
  slePhase κ = SLEPhase.simple := by
-- proof
  apply StatMech.SLE.slePhase_of_le_four h

/--
[slePhase_of_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_of_mem_Ioo_eq
  {κ : ℝ}
-- given
  (h0 : 4 < κ)
  (h1 : κ < 8) :
-- imply
  slePhase κ = SLEPhase.selfTouching := by
-- proof
  apply StatMech.SLE.slePhase_of_mem_Ioo h0 h1

/--
[slePhase_of_eight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_of_eight_le_eq
  {κ : ℝ}
-- given
  (h : 8 ≤ κ) :
-- imply
  slePhase κ = SLEPhase.spaceFilling := by
-- proof
  apply StatMech.SLE.slePhase_of_eight_le h

/--
[slePhase_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_four_eq :
-- imply
  slePhase 4 = SLEPhase.simple := by
-- proof
  apply StatMech.SLE.slePhase_four

/--
[slePhase_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_eight_eq :
-- imply
  slePhase 8 = SLEPhase.spaceFilling := by
-- proof
  apply StatMech.SLE.slePhase_eight

/--
[slePhase_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_zero_eq :
-- imply
  slePhase 0 = SLEPhase.simple := by
-- proof
  apply StatMech.SLE.slePhase_zero

/--
[slePhase_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_six_eq :
-- imply
  slePhase 6 = SLEPhase.selfTouching := by
-- proof
  apply StatMech.SLE.slePhase_six

/--
[slePhase_eq_simple_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_eq_simple_iff_eq
  {κ : ℝ}
-- given
  (hκ : 0 ≤ κ) :
-- imply
  slePhase κ = SLEPhase.simple ↔ IsSimplePhase κ := by
-- proof
  apply StatMech.SLE.slePhase_eq_simple_iff hκ

/--
[slePhase_eq_selfTouching_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_eq_selfTouching_iff_eq
  {κ : ℝ} :
-- imply
  slePhase κ = SLEPhase.selfTouching ↔ IsSelfTouchingPhase κ := by
-- proof
  apply StatMech.SLE.slePhase_eq_selfTouching_iff

/--
[slePhase_eq_spaceFilling_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_eq_spaceFilling_iff_eq
  {κ : ℝ} :
-- imply
  slePhase κ = SLEPhase.spaceFilling ↔ IsSpaceFillingPhase κ := by
-- proof
  apply StatMech.SLE.slePhase_eq_spaceFilling_iff

/--
[slePhase_kappaPercolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_kappaPercolation_eq :
-- imply
  slePhase kappaPercolation = SLEPhase.selfTouching := by
-- proof
  apply StatMech.SLE.slePhase_kappaPercolation

/--
[slePhase_kappaIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma slePhase_kappaIsing_eq :
-- imply
  slePhase kappaIsing = SLEPhase.simple := by
-- proof
  apply StatMech.SLE.slePhase_kappaIsing

/--
[cardyCrossing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma cardyCrossing_eq_eq
  {s : ℝ} :
-- imply
  cardyCrossing s = cardyPrefactor * s ^ ((1 : ℝ) / 3) * ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3) (4 / 3) s := by
-- proof
  apply StatMech.SLE.cardyCrossing_eq s

/--
[cardyCrossing_factor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma cardyCrossing_factor_pos_eq
  {s : ℝ}
-- given
  (hs : 0 < s) :
-- imply
  0 < cardyPrefactor * s ^ ((1 : ℝ) / 3) := by
-- proof
  apply StatMech.SLE.cardyCrossing_factor_pos hs

/--
[cardyHypergeometric_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma cardyHypergeometric_zero_eq :
-- imply
  ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3) (4 / 3) (0 : ℝ) = 1 := by
-- proof
  apply StatMech.SLE.cardyHypergeometric_zero

/--
[mem_cleParameterSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma mem_cleParameterSet_eq
  {κ : ℝ} :
-- imply
  κ ∈ cleParameterSet ↔ IsCLEParameter κ := by
-- proof
  apply StatMech.SLE.mem_cleParameterSet

/--
[cleParameterSet_subset_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma cleParameterSet_subset_pos_eq :
-- imply
  cleParameterSet ⊆ {κ : ℝ | 0 < κ} := by
-- proof
  apply StatMech.SLE.cleParameterSet_subset_pos

/--
[kappaPercolation_mem_cleParameterSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma kappaPercolation_mem_cleParameterSet_eq :
-- imply
  kappaPercolation ∈ cleParameterSet := by
-- proof
  apply StatMech.SLE.kappaPercolation_mem_cleParameterSet

/--
[kappaFKIsing_mem_cleParameterSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma kappaFKIsing_mem_cleParameterSet_eq :
-- imply
  kappaFKIsing ∈ cleParameterSet := by
-- proof
  apply StatMech.SLE.kappaFKIsing_mem_cleParameterSet

/--
[kappaIsing_mem_cleParameterSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma kappaIsing_mem_cleParameterSet_eq :
-- imply
  kappaIsing ∈ cleParameterSet := by
-- proof
  apply StatMech.SLE.kappaIsing_mem_cleParameterSet

/--
[idLoopLaw_invariant_under_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean)
-/
@[path]
private lemma idLoopLaw_invariant_under_id_eq
  [MeasurableSpace Ω]
  {loops : Ω → Set (Set ℂ)}
  {μ : MeasureTheory.Measure Ω} :
-- imply
  Measurable (id : Ω → Ω) ∧ (∀ ω, loops (id ω) = (fun S => (Mobius.id ℂ).apply '' S) '' (loops ω)) → MeasureTheory.Measure.map id μ = μ := by
-- proof
  apply StatMech.SLE.idLoopLaw_invariant_under_id loops μ


-- created on 2026-10-23
