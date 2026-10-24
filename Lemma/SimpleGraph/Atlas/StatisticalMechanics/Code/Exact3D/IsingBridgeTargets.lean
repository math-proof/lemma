import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets
open StatMech StatMech.Exact3D


/--
[PlusXAxisFKConnectionAgrees.congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma congr_eventually_eq
  {β : ℝ}
  {conn comparison : ℕ → ℝ}
-- given
  (hcmp : PlusXAxisFKConnectionAgrees β conn)
  (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
-- imply
  PlusXAxisFKConnectionAgrees β comparison := by
-- proof
  apply StatMech.Exact3D.PlusXAxisFKConnectionAgrees.congr_eventually hcmp hEq

/--
[PlusXAxisFKConnectionAgrees.congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma congr_eventually_iff_eq
  {β : ℝ}
  {conn comparison : ℕ → ℝ}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
-- imply
  PlusXAxisFKConnectionAgrees β conn ↔ PlusXAxisFKConnectionAgrees β comparison := by
-- proof
  apply StatMech.Exact3D.PlusXAxisFKConnectionAgrees.congr_eventually_iff hEq

/--
[FreeXAxisFKConnectionAgrees.congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma congr_eventually_eq_2
  {β : ℝ}
  {conn comparison : ℕ → ℝ}
-- given
  (hcmp : FreeXAxisFKConnectionAgrees β conn)
  (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
-- imply
  FreeXAxisFKConnectionAgrees β comparison := by
-- proof
  apply StatMech.Exact3D.FreeXAxisFKConnectionAgrees.congr_eventually hcmp hEq

/--
[FreeXAxisFKConnectionAgrees.congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma congr_eventually_iff_eq_2
  {β : ℝ}
  {conn comparison : ℕ → ℝ}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
-- imply
  FreeXAxisFKConnectionAgrees β conn ↔ FreeXAxisFKConnectionAgrees β comparison := by
-- proof
  apply StatMech.Exact3D.FreeXAxisFKConnectionAgrees.congr_eventually_iff hEq

/--
[FKXAxisConnectionExactExponentialDecay.congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma congr_eventually_eq_3
  {conn comparison : ℕ → ℝ}
  {A m : ℝ}
-- given
  (hdecay : FKXAxisConnectionExactExponentialDecay conn A m)
  (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
-- imply
  FKXAxisConnectionExactExponentialDecay comparison A m := by
-- proof
  apply StatMech.Exact3D.FKXAxisConnectionExactExponentialDecay.congr_eventually hdecay hEq

/--
[FKXAxisConnectionExactExponentialDecay.congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma congr_eventually_iff_eq_3
  {conn comparison : ℕ → ℝ}
  {A m : ℝ}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
-- imply
  FKXAxisConnectionExactExponentialDecay conn A m ↔ FKXAxisConnectionExactExponentialDecay comparison A m := by
-- proof
  apply StatMech.Exact3D.FKXAxisConnectionExactExponentialDecay.congr_eventually_iff hEq

/--
[FKXAxisConnectionSubexponentialPrefactorDecay.congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma congr_eventually_eq_4
  {conn comparison A : ℕ → ℝ}
  {m : ℝ}
-- given
  (hdecay : FKXAxisConnectionSubexponentialPrefactorDecay conn A m)
  (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
-- imply
  FKXAxisConnectionSubexponentialPrefactorDecay comparison A m := by
-- proof
  apply StatMech.Exact3D.FKXAxisConnectionSubexponentialPrefactorDecay.congr_eventually hdecay hEq

/--
[FKXAxisConnectionSubexponentialPrefactorDecay.congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma congr_eventually_iff_eq_4
  {conn comparison A : ℕ → ℝ}
  {m : ℝ}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
-- imply
  FKXAxisConnectionSubexponentialPrefactorDecay conn A m ↔ FKXAxisConnectionSubexponentialPrefactorDecay comparison A m := by
-- proof
  apply StatMech.Exact3D.FKXAxisConnectionSubexponentialPrefactorDecay.congr_eventually_iff hEq

/--
[FKXAxisConnectionTwoSidedSubexponentialBounds.tendsto_neg_log_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma tendsto_neg_log_div_eq
  {conn Alo Ahi : ℕ → ℝ}
  {m : ℝ}
-- given
  (hbounds : FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
-- imply
  Filter.Tendsto (fun n : ℕ => -Real.log (conn n) / (n : ℝ)) Filter.atTop (nhds m) := by
-- proof
  apply StatMech.Exact3D.FKXAxisConnectionTwoSidedSubexponentialBounds.tendsto_neg_log_div hbounds

/--
[FKXAxisConnectionTwoSidedSubexponentialBounds.mass_eq_of_tendsto_neg_log_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma mass_eq_of_tendsto_neg_log_div_eq
  {conn Alo Ahi : ℕ → ℝ}
  {m rate : ℝ}
-- given
  (hbounds : FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m)
  (hrate : Filter.Tendsto (fun n : ℕ => -Real.log (conn n) / (n : ℝ)) Filter.atTop (nhds rate)) :
-- imply
  m = rate := by
-- proof
  apply StatMech.Exact3D.FKXAxisConnectionTwoSidedSubexponentialBounds.mass_eq_of_tendsto_neg_log_div hbounds hrate

/--
[FKXAxisConnectionTwoSidedSubexponentialBounds.congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma congr_eventually_eq_5
  {conn comparison Alo Ahi : ℕ → ℝ}
  {m : ℝ}
-- given
  (hbounds : FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m)
  (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
-- imply
  FKXAxisConnectionTwoSidedSubexponentialBounds comparison Alo Ahi m := by
-- proof
  apply StatMech.Exact3D.FKXAxisConnectionTwoSidedSubexponentialBounds.congr_eventually hbounds hEq

/--
[FKXAxisConnectionTwoSidedSubexponentialBounds.congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma congr_eventually_iff_eq_5
  {conn comparison Alo Ahi : ℕ → ℝ}
  {m : ℝ}
-- given
  (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
-- imply
  FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m ↔ FKXAxisConnectionTwoSidedSubexponentialBounds comparison Alo Ahi m := by
-- proof
  apply StatMech.Exact3D.FKXAxisConnectionTwoSidedSubexponentialBounds.congr_eventually_iff hEq

/--
[plusPositiveSubcriticalMassBridge_of_subcriticalMassBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusPositiveSubcriticalMassBridge_of_subcriticalMassBridge_eq
-- given
  (h : PlusSubcriticalMassBridge) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.plusPositiveSubcriticalMassBridge_of_subcriticalMassBridge h

/--
[freePositiveSubcriticalMassBridge_of_subcriticalMassBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freePositiveSubcriticalMassBridge_of_subcriticalMassBridge_eq
-- given
  (h : FreeSubcriticalMassBridge) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePositiveSubcriticalMassBridge_of_subcriticalMassBridge h

/--
[plusPositiveSubcriticalCorrelationLengthBridge_of_subcriticalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusPositiveSubcriticalCorrelationLengthBridge_of_subcriticalBridge_eq
-- given
  (h : PlusSubcriticalCorrelationLengthBridge) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusPositiveSubcriticalCorrelationLengthBridge_of_subcriticalBridge h

/--
[freePositiveSubcriticalCorrelationLengthBridge_of_subcriticalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freePositiveSubcriticalCorrelationLengthBridge_of_subcriticalBridge_eq
-- given
  (h : FreeSubcriticalCorrelationLengthBridge) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freePositiveSubcriticalCorrelationLengthBridge_of_subcriticalBridge h

/--
[plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge_eq
-- given
  (hmass : PlusPositiveSubcriticalMassBridge) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge hmass

/--
[freePositiveSubcriticalCorrelationLengthBridge_of_massBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freePositiveSubcriticalCorrelationLengthBridge_of_massBridge_eq
-- given
  (hmass : FreePositiveSubcriticalMassBridge) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freePositiveSubcriticalCorrelationLengthBridge_of_massBridge hmass

/--
[plusSelectedPositiveSubcriticalMass_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalMass_spec_eq
  {β : ℝ}
-- given
  (h : PlusPositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  0 < plusSelectedPositiveSubcriticalMass h β ∧ HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalMass_spec h hβpos hβc

/--
[plusSelectedPositiveSubcriticalMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalMass_pos_eq
  {β : ℝ}
-- given
  (h : PlusPositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  0 < plusSelectedPositiveSubcriticalMass h β := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalMass_pos h hβpos hβc

/--
[plusSelectedPositiveSubcriticalMass_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalMass_hasInverseCorrelationLength_eq
  {β : ℝ}
-- given
  (h : PlusPositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalMass_hasInverseCorrelationLength h hβpos hβc

/--
[plusSelectedPositiveSubcriticalCorrelationLengthFromMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLengthFromMass_pos_eq
  {β : ℝ}
-- given
  (h : PlusPositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  0 < plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLengthFromMass_pos h hβpos hβc

/--
[plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength_eq
  {β : ℝ}
-- given
  (h : PlusPositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength h hβpos hβc

/--
[freeSelectedPositiveSubcriticalMass_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalMass_spec_eq
  {β : ℝ}
-- given
  (h : FreePositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  0 < freeSelectedPositiveSubcriticalMass h β ∧ HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalMass_spec h hβpos hβc

/--
[freeSelectedPositiveSubcriticalMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalMass_pos_eq
  {β : ℝ}
-- given
  (h : FreePositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  0 < freeSelectedPositiveSubcriticalMass h β := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalMass_pos h hβpos hβc

/--
[freeSelectedPositiveSubcriticalMass_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalMass_hasInverseCorrelationLength_eq
  {β : ℝ}
-- given
  (h : FreePositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalMass_hasInverseCorrelationLength h hβpos hβc

/--
[freeSelectedPositiveSubcriticalCorrelationLengthFromMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLengthFromMass_pos_eq
  {β : ℝ}
-- given
  (h : FreePositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  0 < freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLengthFromMass_pos h hβpos hβc

/--
[freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength_eq
  {β : ℝ}
-- given
  (h : FreePositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength h hβpos hβc

/--
[plusSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength_eq
  {β : ℝ}
-- given
  (h : PlusPositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength h hβpos hβc

/--
[freeSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength_eq
  {β : ℝ}
-- given
  (h : FreePositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β = liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength h hβpos hβc

/--
[plusSelectedPositiveSubcriticalCorrelationLength_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLength_spec_eq
  {β : ℝ}
-- given
  (h : PlusPositiveSubcriticalCorrelationLengthBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  0 < plusSelectedPositiveSubcriticalCorrelationLength h β ∧ HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLength_spec h hβpos hβc

/--
[plusSelectedPositiveSubcriticalCorrelationLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLength_pos_eq
  {β : ℝ}
-- given
  (h : PlusPositiveSubcriticalCorrelationLengthBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  0 < plusSelectedPositiveSubcriticalCorrelationLength h β := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLength_pos h hβpos hβc

/--
[plusSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength_eq
  {β : ℝ}
-- given
  (h : PlusPositiveSubcriticalCorrelationLengthBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength h hβpos hβc

/--
[freeSelectedPositiveSubcriticalCorrelationLength_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLength_spec_eq
  {β : ℝ}
-- given
  (h : FreePositiveSubcriticalCorrelationLengthBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  0 < freeSelectedPositiveSubcriticalCorrelationLength h β ∧ HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLength_spec h hβpos hβc

/--
[freeSelectedPositiveSubcriticalCorrelationLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLength_pos_eq
  {β : ℝ}
-- given
  (h : FreePositiveSubcriticalCorrelationLengthBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  0 < freeSelectedPositiveSubcriticalCorrelationLength h β := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLength_pos h hβpos hβc

/--
[freeSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength_eq
  {β : ℝ}
-- given
  (h : FreePositiveSubcriticalCorrelationLengthBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength h hβpos hβc

/--
[plusSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength_eq
  {β : ℝ}
-- given
  (h : PlusPositiveSubcriticalCorrelationLengthBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  plusSelectedPositiveSubcriticalCorrelationLength h β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength h hβpos hβc

/--
[freeSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength_eq
  {β : ℝ}
-- given
  (h : FreePositiveSubcriticalCorrelationLengthBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  freeSelectedPositiveSubcriticalCorrelationLength h β = liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength h hβpos hβc

/--
[eventually_mem_positiveSubcriticalWindow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_mem_positiveSubcriticalWindow_eq
  {δ : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.eventually_mem_positiveSubcriticalWindow hδ

/--
[beta_pos_of_mem_positiveSubcriticalWindow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma beta_pos_of_mem_positiveSubcriticalWindow_eq
  {δ β : ℝ}
-- given
  (hδle : δ ≤ Ising.betaC 3)
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
-- imply
  0 < β := by
-- proof
  apply StatMech.Exact3D.beta_pos_of_mem_positiveSubcriticalWindow hδle hβ

/--
[eventually_plusSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength_eq
  {δ : ℝ}
-- given
  (h : PlusPositiveSubcriticalMassBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength h hδ hδle

/--
[eventually_freeSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength_eq
  {δ : ℝ}
-- given
  (h : FreePositiveSubcriticalMassBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β = liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength h hδ hδle

/--
[eventually_plusSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength_eq
  {δ : ℝ}
-- given
  (h : PlusPositiveSubcriticalCorrelationLengthBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), plusSelectedPositiveSubcriticalCorrelationLength h β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength h hδ hδle

/--
[eventually_freeSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength_eq
  {δ : ℝ}
-- given
  (h : FreePositiveSubcriticalCorrelationLengthBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength h β = liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength h hδ hδle

/--
[plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminf_eq
  {δ ν : ℝ}
-- given
  (h : PlusPositiveSubcriticalMassBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  HasCriticalNu Ising3DModel (plusSelectedPositiveSubcriticalCorrelationLengthFromMass h) ν ↔ HasCriticalNu Ising3DModel (fun β => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminf h hδ hδle

/--
[freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminf_eq
  {δ ν : ℝ}
-- given
  (h : FreePositiveSubcriticalMassBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  HasCriticalNu Ising3DFreeModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass h) ν ↔ HasCriticalNu Ising3DFreeModel (fun β => liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminf h hδ hδle

/--
[plusSelectedPositiveSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength_eq
  {δ ν : ℝ}
-- given
  (h : PlusPositiveSubcriticalCorrelationLengthBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  HasCriticalNu Ising3DModel (plusSelectedPositiveSubcriticalCorrelationLength h) ν ↔ HasCriticalNu Ising3DModel (fun β => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength h hδ hδle

/--
[freeSelectedPositiveSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength_eq
  {δ ν : ℝ}
-- given
  (h : FreePositiveSubcriticalCorrelationLengthBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  HasCriticalNu Ising3DFreeModel (freeSelectedPositiveSubcriticalCorrelationLength h) ν ↔ HasCriticalNu Ising3DFreeModel (fun β => liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength h hδ hδle

/--
[plusSelectedSubcriticalMass_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalMass_spec_eq
  {β : ℝ}
-- given
  (h : PlusSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  0 < plusSelectedSubcriticalMass h β ∧ HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalMass_spec h hβ

/--
[plusSelectedSubcriticalMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalMass_pos_eq
  {β : ℝ}
-- given
  (h : PlusSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  0 < plusSelectedSubcriticalMass h β := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalMass_pos h hβ

/--
[plusSelectedSubcriticalMass_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalMass_hasInverseCorrelationLength_eq
  {β : ℝ}
-- given
  (h : PlusSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalMass_hasInverseCorrelationLength h hβ

/--
[plusSelectedSubcriticalCorrelationLengthFromMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLengthFromMass_pos_eq
  {β : ℝ}
-- given
  (h : PlusSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  0 < plusSelectedSubcriticalCorrelationLengthFromMass h β := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLengthFromMass_pos h hβ

/--
[plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength_eq
  {β : ℝ}
-- given
  (h : PlusSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength h hβ

/--
[freeSelectedSubcriticalMass_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalMass_spec_eq
  {β : ℝ}
-- given
  (h : FreeSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  0 < freeSelectedSubcriticalMass h β ∧ HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalMass_spec h hβ

/--
[freeSelectedSubcriticalMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalMass_pos_eq
  {β : ℝ}
-- given
  (h : FreeSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  0 < freeSelectedSubcriticalMass h β := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalMass_pos h hβ

/--
[freeSelectedSubcriticalMass_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalMass_hasInverseCorrelationLength_eq
  {β : ℝ}
-- given
  (h : FreeSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalMass_hasInverseCorrelationLength h hβ

/--
[freeSelectedSubcriticalCorrelationLengthFromMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLengthFromMass_pos_eq
  {β : ℝ}
-- given
  (h : FreeSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  0 < freeSelectedSubcriticalCorrelationLengthFromMass h β := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLengthFromMass_pos h hβ

/--
[freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength_eq
  {β : ℝ}
-- given
  (h : FreeSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength h hβ

/--
[plusSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength_eq
  {β : ℝ}
-- given
  (h : PlusSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  plusSelectedSubcriticalCorrelationLengthFromMass h β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength h hβ

/--
[freeSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength_eq
  {β : ℝ}
-- given
  (h : FreeSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  freeSelectedSubcriticalCorrelationLengthFromMass h β = liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength h hβ

/--
[plusSelectedSubcriticalCorrelationLength_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLength_spec_eq
  {β : ℝ}
-- given
  (h : PlusSubcriticalCorrelationLengthBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  0 < plusSelectedSubcriticalCorrelationLength h β ∧ HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLength_spec h hβ

/--
[plusSelectedSubcriticalCorrelationLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLength_pos_eq
  {β : ℝ}
-- given
  (h : PlusSubcriticalCorrelationLengthBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  0 < plusSelectedSubcriticalCorrelationLength h β := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLength_pos h hβ

/--
[plusSelectedSubcriticalCorrelationLength_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLength_hasCorrelationLength_eq
  {β : ℝ}
-- given
  (h : PlusSubcriticalCorrelationLengthBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLength_hasCorrelationLength h hβ

/--
[freeSelectedSubcriticalCorrelationLength_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLength_spec_eq
  {β : ℝ}
-- given
  (h : FreeSubcriticalCorrelationLengthBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  0 < freeSelectedSubcriticalCorrelationLength h β ∧ HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLength_spec h hβ

/--
[freeSelectedSubcriticalCorrelationLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLength_pos_eq
  {β : ℝ}
-- given
  (h : FreeSubcriticalCorrelationLengthBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  0 < freeSelectedSubcriticalCorrelationLength h β := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLength_pos h hβ

/--
[freeSelectedSubcriticalCorrelationLength_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLength_hasCorrelationLength_eq
  {β : ℝ}
-- given
  (h : FreeSubcriticalCorrelationLengthBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLength_hasCorrelationLength h hβ

/--
[plusSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength_eq
  {β : ℝ}
-- given
  (h : PlusSubcriticalCorrelationLengthBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  plusSelectedSubcriticalCorrelationLength h β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength h hβ

/--
[freeSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength_eq
  {β : ℝ}
-- given
  (h : FreeSubcriticalCorrelationLengthBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  freeSelectedSubcriticalCorrelationLength h β = liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength h hβ

/--
[eventually_plusSelectedSubcriticalMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalMass_pos_eq
-- given
  (h : PlusSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < plusSelectedSubcriticalMass h β := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalMass_pos h

/--
[eventually_plusSelectedSubcriticalMass_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalMass_hasInverseCorrelationLength_eq
-- given
  (h : PlusSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalMass_hasInverseCorrelationLength h

/--
[eventually_plusSelectedSubcriticalCorrelationLengthFromMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalCorrelationLengthFromMass_pos_eq
-- given
  (h : PlusSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < plusSelectedSubcriticalCorrelationLengthFromMass h β := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalCorrelationLengthFromMass_pos h

/--
[eventually_plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength_eq
-- given
  (h : PlusSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength h

/--
[eventually_plusSelectedSubcriticalCorrelationLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalCorrelationLength_pos_eq
-- given
  (h : PlusSubcriticalCorrelationLengthBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < plusSelectedSubcriticalCorrelationLength h β := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalCorrelationLength_pos h

/--
[eventually_plusSelectedSubcriticalCorrelationLength_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalCorrelationLength_hasCorrelationLength_eq
-- given
  (h : PlusSubcriticalCorrelationLengthBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalCorrelationLength_hasCorrelationLength h

/--
[eventually_freeSelectedSubcriticalMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalMass_pos_eq
-- given
  (h : FreeSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < freeSelectedSubcriticalMass h β := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalMass_pos h

/--
[eventually_freeSelectedSubcriticalMass_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalMass_hasInverseCorrelationLength_eq
-- given
  (h : FreeSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalMass_hasInverseCorrelationLength h

/--
[eventually_freeSelectedSubcriticalCorrelationLengthFromMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalCorrelationLengthFromMass_pos_eq
-- given
  (h : FreeSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < freeSelectedSubcriticalCorrelationLengthFromMass h β := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalCorrelationLengthFromMass_pos h

/--
[eventually_freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength_eq
-- given
  (h : FreeSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength h

/--
[eventually_freeSelectedSubcriticalCorrelationLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalCorrelationLength_pos_eq
-- given
  (h : FreeSubcriticalCorrelationLengthBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < freeSelectedSubcriticalCorrelationLength h β := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalCorrelationLength_pos h

/--
[eventually_freeSelectedSubcriticalCorrelationLength_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalCorrelationLength_hasCorrelationLength_eq
-- given
  (h : FreeSubcriticalCorrelationLengthBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalCorrelationLength_hasCorrelationLength h

/--
[eventually_plusSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength_eq
-- given
  (h : PlusSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), plusSelectedSubcriticalCorrelationLengthFromMass h β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength h

/--
[eventually_freeSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength_eq
-- given
  (h : FreeSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedSubcriticalCorrelationLengthFromMass h β = liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength h

/--
[eventually_plusSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength_eq
-- given
  (h : PlusSubcriticalCorrelationLengthBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), plusSelectedSubcriticalCorrelationLength h β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength h

/--
[eventually_freeSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength_eq
-- given
  (h : FreeSubcriticalCorrelationLengthBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedSubcriticalCorrelationLength h β = liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength h

/--
[plusSelectedSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminfCorrelationLength_eq
  {ν : ℝ}
-- given
  (h : PlusSubcriticalMassBridge) :
-- imply
  HasCriticalNu Ising3DModel (plusSelectedSubcriticalCorrelationLengthFromMass h) ν ↔ HasCriticalNu Ising3DModel (fun β => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminfCorrelationLength h

/--
[freeSelectedSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminfCorrelationLength_eq
  {ν : ℝ}
-- given
  (h : FreeSubcriticalMassBridge) :
-- imply
  HasCriticalNu Ising3DFreeModel (freeSelectedSubcriticalCorrelationLengthFromMass h) ν ↔ HasCriticalNu Ising3DFreeModel (fun β => liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminfCorrelationLength h

/--
[plusSelectedSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength_eq
  {ν : ℝ}
-- given
  (h : PlusSubcriticalCorrelationLengthBridge) :
-- imply
  HasCriticalNu Ising3DModel (plusSelectedSubcriticalCorrelationLength h) ν ↔ HasCriticalNu Ising3DModel (fun β => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength h

/--
[freeSelectedSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength_eq
  {ν : ℝ}
-- given
  (h : FreeSubcriticalCorrelationLengthBridge) :
-- imply
  HasCriticalNu Ising3DFreeModel (freeSelectedSubcriticalCorrelationLength h) ν ↔ HasCriticalNu Ising3DFreeModel (fun β => liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength h

/--
[Ising3DFreeModel_twoPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma Ising3DFreeModel_twoPoint_eq_eq
  {β : ℝ}
  {x y : Ising3DSite} :
-- imply
  TwoPointFunction Ising3DFreeModel β x y = ising3DFreeTwoPoint β x y := by
-- proof
  apply StatMech.Exact3D.Ising3DFreeModel_twoPoint_eq β x y

/--
[Ising3DFreeModel_betaC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma Ising3DFreeModel_betaC_eq_eq :
-- imply
  Ising3DFreeModel.betaC = Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.Ising3DFreeModel_betaC_eq

/--
[Ising3DFreeModel_inverseDecayRate_xAxis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma Ising3DFreeModel_inverseDecayRate_xAxis_eq_eq
  {β : ℝ}
  {n : ℕ} :
-- imply
  inverseDecayRate Ising3DFreeModel β ising3DOrigin ising3DXAxisRay n = freeInverseDecayRateOnXAxis β n := by
-- proof
  apply StatMech.Exact3D.Ising3DFreeModel_inverseDecayRate_xAxis_eq β n

/--
[Ising3DFreeModel_lowerInverseCorrelationLength_xAxis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma Ising3DFreeModel_lowerInverseCorrelationLength_xAxis_eq_eq
  {β : ℝ} :
-- imply
  lowerInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay = freeLowerInverseCorrelationLengthOnXAxis β := by
-- proof
  apply StatMech.Exact3D.Ising3DFreeModel_lowerInverseCorrelationLength_xAxis_eq β

/--
[Ising3DFreeModel_upperInverseCorrelationLength_xAxis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma Ising3DFreeModel_upperInverseCorrelationLength_xAxis_eq_eq
  {β : ℝ} :
-- imply
  upperInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay = freeUpperInverseCorrelationLengthOnXAxis β := by
-- proof
  apply StatMech.Exact3D.Ising3DFreeModel_upperInverseCorrelationLength_xAxis_eq β

/--
[Ising3DFreeModel_liminfCorrelationLength_xAxis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma Ising3DFreeModel_liminfCorrelationLength_xAxis_eq_eq
  {β : ℝ} :
-- imply
  liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay = freeLiminfCorrelationLengthOnXAxis β := by
-- proof
  apply StatMech.Exact3D.Ising3DFreeModel_liminfCorrelationLength_xAxis_eq β

/--
[plus_hasInverseCorrelationLength_xAxis_of_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_exactExponential_eq
  {β A m : ℝ}
-- given
  (hA : 0 < A)
  (hG : PlusXAxisExactExponentialDecay β A m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_exactExponential hA hG

/--
[free_hasInverseCorrelationLength_xAxis_of_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_exactExponential_eq
  {β A m : ℝ}
-- given
  (hA : 0 < A)
  (hG : FreeXAxisExactExponentialDecay β A m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_exactExponential hA hG

/--
[plus_hasCorrelationLength_xAxis_of_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_exactExponential_eq
  {β A m : ℝ}
-- given
  (hA : 0 < A)
  (hm : 0 < m)
  (hG : PlusXAxisExactExponentialDecay β A m) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_exactExponential hA hm hG

/--
[free_hasCorrelationLength_xAxis_of_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_exactExponential_eq
  {β A m : ℝ}
-- given
  (hA : 0 < A)
  (hm : 0 < m)
  (hG : FreeXAxisExactExponentialDecay β A m) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_exactExponential hA hm hG

/--
[plus_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hG : PlusXAxisSubexponentialPrefactorDecay β A m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor hG

/--
[free_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hG : FreeXAxisSubexponentialPrefactorDecay β A m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor hG

/--
[plus_hasCorrelationLength_xAxis_of_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hm : 0 < m)
  (hG : PlusXAxisSubexponentialPrefactorDecay β A m) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_subexponentialPrefactor hm hG

/--
[free_hasCorrelationLength_xAxis_of_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hm : 0 < m)
  (hG : FreeXAxisSubexponentialPrefactorDecay β A m) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_subexponentialPrefactor hm hG

/--
[plus_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hG : PlusXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds hG

/--
[free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hG : FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds hG

/--
[plus_hasCorrelationLength_xAxis_of_twoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_twoSidedSubexponentialBounds_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hm : 0 < m)
  (hG : PlusXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_twoSidedSubexponentialBounds hm hG

/--
[free_hasCorrelationLength_xAxis_of_twoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_twoSidedSubexponentialBounds_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hm : 0 < m)
  (hG : FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_twoSidedSubexponentialBounds hm hG

/--
[plusXAxisExactExponentialDecay_of_fkConnectionComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusXAxisExactExponentialDecay_of_fkConnectionComparison_eq
  {β A m : ℝ}
  {conn : ℕ → ℝ}
-- given
  (hcmp : PlusXAxisFKConnectionAgrees β conn)
  (hconn : FKXAxisConnectionExactExponentialDecay conn A m) :
-- imply
  PlusXAxisExactExponentialDecay β A m := by
-- proof
  apply StatMech.Exact3D.plusXAxisExactExponentialDecay_of_fkConnectionComparison hcmp hconn

/--
[freeXAxisExactExponentialDecay_of_fkConnectionComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeXAxisExactExponentialDecay_of_fkConnectionComparison_eq
  {β A m : ℝ}
  {conn : ℕ → ℝ}
-- given
  (hcmp : FreeXAxisFKConnectionAgrees β conn)
  (hconn : FKXAxisConnectionExactExponentialDecay conn A m) :
-- imply
  FreeXAxisExactExponentialDecay β A m := by
-- proof
  apply StatMech.Exact3D.freeXAxisExactExponentialDecay_of_fkConnectionComparison hcmp hconn

/--
[plusXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison_eq
  {β m : ℝ}
  {conn A : ℕ → ℝ}
-- given
  (hcmp : PlusXAxisFKConnectionAgrees β conn)
  (hconn : FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
-- imply
  PlusXAxisSubexponentialPrefactorDecay β A m := by
-- proof
  apply StatMech.Exact3D.plusXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison hcmp hconn

/--
[freeXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison_eq
  {β m : ℝ}
  {conn A : ℕ → ℝ}
-- given
  (hcmp : FreeXAxisFKConnectionAgrees β conn)
  (hconn : FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
-- imply
  FreeXAxisSubexponentialPrefactorDecay β A m := by
-- proof
  apply StatMech.Exact3D.freeXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison hcmp hconn

/--
[plusXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison_eq
  {β m : ℝ}
  {conn Alo Ahi : ℕ → ℝ}
-- given
  (hcmp : PlusXAxisFKConnectionAgrees β conn)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
-- imply
  PlusXAxisTwoSidedSubexponentialBounds β Alo Ahi m := by
-- proof
  apply StatMech.Exact3D.plusXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison hcmp hconn

/--
[freeXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison_eq
  {β m : ℝ}
  {conn Alo Ahi : ℕ → ℝ}
-- given
  (hcmp : FreeXAxisFKConnectionAgrees β conn)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
-- imply
  FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi m := by
-- proof
  apply StatMech.Exact3D.freeXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison hcmp hconn

/--
[plus_hasInverseCorrelationLength_of_free_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_of_free_agree_eq
  {β m : ℝ}
  {origin : Ising3DSite}
  {ray : ℕ → Ising3DSite}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3)
  (hfree : HasInverseCorrelationLength Ising3DFreeModel β origin ray m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β origin ray m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_of_free_agree hagree hβ hfree

/--
[plus_hasCorrelationLength_of_free_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_of_free_agree_eq
  {β ξ : ℝ}
  {origin : Ising3DSite}
  {ray : ℕ → Ising3DSite}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3)
  (hfree : HasCorrelationLength Ising3DFreeModel β origin ray ξ) :
-- imply
  HasCorrelationLength Ising3DModel β origin ray ξ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_of_free_agree hagree hβ hfree

/--
[free_hasInverseCorrelationLength_of_plus_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_of_plus_agree_eq
  {β m : ℝ}
  {origin : Ising3DSite}
  {ray : ℕ → Ising3DSite}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3)
  (hplus : HasInverseCorrelationLength Ising3DModel β origin ray m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β origin ray m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_of_plus_agree hagree hβ hplus

/--
[free_hasCorrelationLength_of_plus_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma free_hasCorrelationLength_of_plus_agree_eq
  {β ξ : ℝ}
  {origin : Ising3DSite}
  {ray : ℕ → Ising3DSite}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3)
  (hplus : HasCorrelationLength Ising3DModel β origin ray ξ) :
-- imply
  HasCorrelationLength Ising3DFreeModel β origin ray ξ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_of_plus_agree hagree hβ hplus

/--
[hasInverseCorrelationLength_plus_free_agree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma hasInverseCorrelationLength_plus_free_agree_iff_eq
  {β m : ℝ}
  {origin : Ising3DSite}
  {ray : ℕ → Ising3DSite}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasInverseCorrelationLength Ising3DModel β origin ray m ↔ HasInverseCorrelationLength Ising3DFreeModel β origin ray m := by
-- proof
  apply StatMech.Exact3D.hasInverseCorrelationLength_plus_free_agree_iff hagree hβ

/--
[hasCorrelationLength_plus_free_agree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma hasCorrelationLength_plus_free_agree_iff_eq
  {β ξ : ℝ}
  {origin : Ising3DSite}
  {ray : ℕ → Ising3DSite}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DModel β origin ray ξ ↔ HasCorrelationLength Ising3DFreeModel β origin ray ξ := by
-- proof
  apply StatMech.Exact3D.hasCorrelationLength_plus_free_agree_iff hagree hβ

/--
[plus_hasInverseCorrelationLength_xAxis_of_free_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_free_agree_eq
  {β m : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3)
  (hfree : HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβ hfree

/--
[plus_hasCorrelationLength_xAxis_of_free_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_free_agree_eq
  {β ξ : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3)
  (hfree : HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay ξ) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay ξ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_free_agree hagree hβ hfree

/--
[free_hasInverseCorrelationLength_xAxis_of_plus_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_plus_agree_eq
  {β m : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3)
  (hplus : HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_plus_agree hagree hβ hplus

/--
[free_hasCorrelationLength_xAxis_of_plus_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_plus_agree_eq
  {β ξ : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3)
  (hplus : HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay ξ) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay ξ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_plus_agree hagree hβ hplus

/--
[hasInverseCorrelationLength_xAxis_plus_free_agree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma hasInverseCorrelationLength_xAxis_plus_free_agree_iff_eq
  {β m : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m ↔ HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.hasInverseCorrelationLength_xAxis_plus_free_agree_iff hagree hβ

/--
[hasCorrelationLength_xAxis_plus_free_agree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma hasCorrelationLength_xAxis_plus_free_agree_iff_eq
  {β ξ : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay ξ ↔ HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay ξ := by
-- proof
  apply StatMech.Exact3D.hasCorrelationLength_xAxis_plus_free_agree_iff hagree hβ

/--
[liminfCorrelationLength_plus_eq_free_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma liminfCorrelationLength_plus_eq_free_of_agree_eq
  {β : ℝ}
  {origin : Ising3DSite}
  {ray : ℕ → Ising3DSite}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβ : β < Ising.betaC 3) :
-- imply
  liminfCorrelationLength Ising3DModel β origin ray = liminfCorrelationLength Ising3DFreeModel β origin ray := by
-- proof
  apply StatMech.Exact3D.liminfCorrelationLength_plus_eq_free_of_agree hagree hβ

/--
[eventually_liminfCorrelationLength_xAxis_plus_eq_free_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_liminfCorrelationLength_xAxis_plus_eq_free_of_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.eventually_liminfCorrelationLength_xAxis_plus_eq_free_of_agree hagree

/--
[liminfCorrelationLength_xAxis_hasCriticalNu_plus_free_agree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma liminfCorrelationLength_xAxis_hasCriticalNu_plus_free_agree_iff_eq
  {ν : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
-- imply
  HasCriticalNu Ising3DModel (fun β => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) ν ↔ HasCriticalNu Ising3DFreeModel (fun β => liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.liminfCorrelationLength_xAxis_hasCriticalNu_plus_free_agree_iff hagree

/--
[freePosSubcriticalLengthFromMass_hasCriticalNu_iff_plus_liminf_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freePosSubcriticalLengthFromMass_hasCriticalNu_iff_plus_liminf_of_agree_eq
  {δ ν : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreePositiveSubcriticalMassBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  HasCriticalNu Ising3DFreeModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass h) ν ↔ HasCriticalNu Ising3DModel (fun β => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalLengthFromMass_hasCriticalNu_iff_plus_liminf_of_agree hagree h hδ hδle

/--
[freePosSubcriticalLength_hasCriticalNu_iff_plus_liminf_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freePosSubcriticalLength_hasCriticalNu_iff_plus_liminf_of_agree_eq
  {δ ν : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreePositiveSubcriticalCorrelationLengthBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  HasCriticalNu Ising3DFreeModel (freeSelectedPositiveSubcriticalCorrelationLength h) ν ↔ HasCriticalNu Ising3DModel (fun β => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalLength_hasCriticalNu_iff_plus_liminf_of_agree hagree h hδ hδle

/--
[plusPosSubcriticalLengthFromMass_hasCriticalNu_iff_free_liminf_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusPosSubcriticalLengthFromMass_hasCriticalNu_iff_free_liminf_of_agree_eq
  {δ ν : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusPositiveSubcriticalMassBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  HasCriticalNu Ising3DModel (plusSelectedPositiveSubcriticalCorrelationLengthFromMass h) ν ↔ HasCriticalNu Ising3DFreeModel (fun β => liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.plusPosSubcriticalLengthFromMass_hasCriticalNu_iff_free_liminf_of_agree hagree h hδ hδle

/--
[plusPosSubcriticalLength_hasCriticalNu_iff_free_liminf_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusPosSubcriticalLength_hasCriticalNu_iff_free_liminf_of_agree_eq
  {δ ν : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusPositiveSubcriticalCorrelationLengthBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  HasCriticalNu Ising3DModel (plusSelectedPositiveSubcriticalCorrelationLength h) ν ↔ HasCriticalNu Ising3DFreeModel (fun β => liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay) ν := by
-- proof
  apply StatMech.Exact3D.plusPosSubcriticalLength_hasCriticalNu_iff_free_liminf_of_agree hagree h hδ hδle

/--
[freeSelectedSubcriticalMass_hasPlusInverseCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalMass_hasPlusInverseCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreeSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalMass_hasPlusInverseCorrelationLength_of_agree hagree h hβ

/--
[freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreeSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree hagree h hβ

/--
[freeSelectedSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreeSubcriticalCorrelationLengthBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree hagree h hβ

/--
[eventually_freeSelectedSubcriticalMass_hasPlusInverseCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalMass_hasPlusInverseCorrelationLength_of_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreeSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalMass_hasPlusInverseCorrelationLength_of_agree hagree h

/--
[eventually_freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreeSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree hagree h

/--
[eventually_freeSelectedSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreeSubcriticalCorrelationLengthBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree hagree h

/--
[plusSelectedSubcriticalMass_hasFreeInverseCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalMass_hasFreeInverseCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalMass_hasFreeInverseCorrelationLength_of_agree hagree h hβ

/--
[plusSelectedSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusSubcriticalMassBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree hagree h hβ

/--
[plusSelectedSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusSubcriticalCorrelationLengthBridge)
  (hβ : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree hagree h hβ

/--
[eventually_plusSelectedSubcriticalMass_hasFreeInverseCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalMass_hasFreeInverseCorrelationLength_of_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalMass_hasFreeInverseCorrelationLength_of_agree hagree h

/--
[eventually_plusSelectedSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusSubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree hagree h

/--
[eventually_plusSelectedSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusSubcriticalCorrelationLengthBridge) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree hagree h

/--
[freeSelectedPositiveSubcriticalMass_hasPlusInverseCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalMass_hasPlusInverseCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreePositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalMass_hasPlusInverseCorrelationLength_of_agree hagree h hβpos hβc

/--
[freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreePositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree hagree h hβpos hβc

/--
[freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreePositiveSubcriticalCorrelationLengthBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree hagree h hβpos hβc

/--
[plusSelectedPositiveSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusPositiveSubcriticalCorrelationLengthBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree hagree h hβpos hβc

/--
[plusSelectedPositiveSubcriticalMass_hasFreeInverseCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalMass_hasFreeInverseCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusPositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalMass_hasFreeInverseCorrelationLength_of_agree hagree h hβpos hβc

/--
[plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree_eq
  {β : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusPositiveSubcriticalMassBridge)
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree hagree h hβpos hβc

/--
[eventually_freeSelectedPositiveSubcriticalMass_hasPlusInverseCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedPositiveSubcriticalMass_hasPlusInverseCorrelationLength_of_agree_eq
  {δ : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreePositiveSubcriticalMassBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedPositiveSubcriticalMass_hasPlusInverseCorrelationLength_of_agree hagree h hδ hδle

/--
[eventually_freePosSubcriticalLengthFromMass_hasPlusCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freePosSubcriticalLengthFromMass_hasPlusCorrelationLength_of_agree_eq
  {δ : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreePositiveSubcriticalMassBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_freePosSubcriticalLengthFromMass_hasPlusCorrelationLength_of_agree hagree h hδ hδle

/--
[eventually_plusSelectedPositiveSubcriticalMass_hasFreeInverseCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedPositiveSubcriticalMass_hasFreeInverseCorrelationLength_of_agree_eq
  {δ : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusPositiveSubcriticalMassBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedPositiveSubcriticalMass_hasFreeInverseCorrelationLength_of_agree hagree h hδ hδle

/--
[eventually_plusPosSubcriticalLengthFromMass_hasFreeCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusPosSubcriticalLengthFromMass_hasFreeCorrelationLength_of_agree_eq
  {δ : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusPositiveSubcriticalMassBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β) := by
-- proof
  apply StatMech.Exact3D.eventually_plusPosSubcriticalLengthFromMass_hasFreeCorrelationLength_of_agree hagree h hδ hδle

/--
[eventually_freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree_eq
  {δ : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreePositiveSubcriticalCorrelationLengthBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (freeSelectedPositiveSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.eventually_freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree hagree h hδ hδle

/--
[eventually_plusSelectedPositiveSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma eventually_plusSelectedPositiveSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree_eq
  {δ : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : PlusPositiveSubcriticalCorrelationLengthBridge)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (plusSelectedPositiveSubcriticalCorrelationLength h β) := by
-- proof
  apply StatMech.Exact3D.eventually_plusSelectedPositiveSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree hagree h hδ hδle

/--
[plusSubcriticalMassBridge_of_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalMassBridge_of_exactExponential_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ A m, 0 < A ∧ 0 < m ∧ PlusXAxisExactExponentialDecay β A m) :
-- imply
  PlusSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalMassBridge_of_exactExponential h

/--
[freeSubcriticalMassBridge_of_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalMassBridge_of_exactExponential_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ A m, 0 < A ∧ 0 < m ∧ FreeXAxisExactExponentialDecay β A m) :
-- imply
  FreeSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalMassBridge_of_exactExponential h

/--
[plusSubcriticalMassBridge_of_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalMassBridge_of_subexponentialPrefactor_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (A : ℕ → ℝ) (m : ℝ), 0 < m ∧ PlusXAxisSubexponentialPrefactorDecay β A m) :
-- imply
  PlusSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalMassBridge_of_subexponentialPrefactor h

/--
[freeSubcriticalMassBridge_of_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalMassBridge_of_subexponentialPrefactor_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (A : ℕ → ℝ) (m : ℝ), 0 < m ∧ FreeXAxisSubexponentialPrefactorDecay β A m) :
-- imply
  FreeSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalMassBridge_of_subexponentialPrefactor h

/--
[plusSubcriticalMassBridge_of_twoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalMassBridge_of_twoSidedSubexponentialBounds_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧ PlusXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
-- imply
  PlusSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalMassBridge_of_twoSidedSubexponentialBounds h

/--
[freeSubcriticalMassBridge_of_twoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalMassBridge_of_twoSidedSubexponentialBounds_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧ FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
-- imply
  FreeSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalMassBridge_of_twoSidedSubexponentialBounds h

/--
[plusSubcriticalMassBridge_of_fkConnectionExactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalMassBridge_of_fkConnectionExactExponential_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn : ℕ → ℝ) (A m : ℝ), 0 < A ∧ 0 < m ∧ PlusXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionExactExponentialDecay conn A m) :
-- imply
  PlusSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalMassBridge_of_fkConnectionExactExponential h

/--
[freeSubcriticalMassBridge_of_fkConnectionExactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalMassBridge_of_fkConnectionExactExponential_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn : ℕ → ℝ) (A m : ℝ), 0 < A ∧ 0 < m ∧ FreeXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionExactExponentialDecay conn A m) :
-- imply
  FreeSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalMassBridge_of_fkConnectionExactExponential h

/--
[plusSubcriticalMassBridge_of_fkConnectionSubexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalMassBridge_of_fkConnectionSubexponentialPrefactor_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn A : ℕ → ℝ) (m : ℝ), 0 < m ∧ PlusXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
-- imply
  PlusSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalMassBridge_of_fkConnectionSubexponentialPrefactor h

/--
[freeSubcriticalMassBridge_of_fkConnectionSubexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalMassBridge_of_fkConnectionSubexponentialPrefactor_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn A : ℕ → ℝ) (m : ℝ), 0 < m ∧ FreeXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
-- imply
  FreeSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalMassBridge_of_fkConnectionSubexponentialPrefactor h

/--
[plusSubcriticalMassBridge_of_fkConnectionTwoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalMassBridge_of_fkConnectionTwoSidedSubexponentialBounds_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧ PlusXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
-- imply
  PlusSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalMassBridge_of_fkConnectionTwoSidedSubexponentialBounds h

/--
[freeSubcriticalMassBridge_of_fkConnectionTwoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalMassBridge_of_fkConnectionTwoSidedSubexponentialBounds_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧ FreeXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
-- imply
  FreeSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalMassBridge_of_fkConnectionTwoSidedSubexponentialBounds h

/--
[plusSubcriticalMassBridge_of_free_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalMassBridge_of_free_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeSubcriticalMassBridge) :
-- imply
  PlusSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalMassBridge_of_free_and_agree hagree hfree

/--
[freeSubcriticalMassBridge_of_plus_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalMassBridge_of_plus_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hplus : PlusSubcriticalMassBridge) :
-- imply
  FreeSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalMassBridge_of_plus_and_agree hagree hplus

/--
[subcriticalMassBridge_plus_free_agree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma subcriticalMassBridge_plus_free_agree_iff_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
-- imply
  PlusSubcriticalMassBridge ↔ FreeSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.subcriticalMassBridge_plus_free_agree_iff hagree

/--
[plusPositiveSubcriticalMassBridge_of_free_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusPositiveSubcriticalMassBridge_of_free_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreePositiveSubcriticalMassBridge) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.plusPositiveSubcriticalMassBridge_of_free_and_agree hagree hfree

/--
[freePositiveSubcriticalMassBridge_of_plus_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freePositiveSubcriticalMassBridge_of_plus_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hplus : PlusPositiveSubcriticalMassBridge) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePositiveSubcriticalMassBridge_of_plus_and_agree hagree hplus

/--
[positiveSubcriticalMassBridge_plus_free_agree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma positiveSubcriticalMassBridge_plus_free_agree_iff_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
-- imply
  PlusPositiveSubcriticalMassBridge ↔ FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.positiveSubcriticalMassBridge_plus_free_agree_iff hagree

/--
[plusSubcriticalCorrelationLengthBridge_of_massBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalCorrelationLengthBridge_of_massBridge_eq
-- given
  (hmass : PlusSubcriticalMassBridge) :
-- imply
  PlusSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalCorrelationLengthBridge_of_massBridge hmass

/--
[freeSubcriticalCorrelationLengthBridge_of_massBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalCorrelationLengthBridge_of_massBridge_eq
-- given
  (hmass : FreeSubcriticalMassBridge) :
-- imply
  FreeSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalCorrelationLengthBridge_of_massBridge hmass

/--
[plusSubcriticalCorrelationLengthBridge_of_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalCorrelationLengthBridge_of_exactExponential_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ A m, 0 < A ∧ 0 < m ∧ PlusXAxisExactExponentialDecay β A m) :
-- imply
  PlusSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalCorrelationLengthBridge_of_exactExponential h

/--
[freeSubcriticalCorrelationLengthBridge_of_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalCorrelationLengthBridge_of_exactExponential_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ A m, 0 < A ∧ 0 < m ∧ FreeXAxisExactExponentialDecay β A m) :
-- imply
  FreeSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalCorrelationLengthBridge_of_exactExponential h

/--
[plusSubcriticalCorrelationLengthBridge_of_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalCorrelationLengthBridge_of_subexponentialPrefactor_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (A : ℕ → ℝ) (m : ℝ), 0 < m ∧ PlusXAxisSubexponentialPrefactorDecay β A m) :
-- imply
  PlusSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalCorrelationLengthBridge_of_subexponentialPrefactor h

/--
[freeSubcriticalCorrelationLengthBridge_of_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalCorrelationLengthBridge_of_subexponentialPrefactor_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (A : ℕ → ℝ) (m : ℝ), 0 < m ∧ FreeXAxisSubexponentialPrefactorDecay β A m) :
-- imply
  FreeSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalCorrelationLengthBridge_of_subexponentialPrefactor h

/--
[plusSubcriticalCorrelationLengthBridge_of_twoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalCorrelationLengthBridge_of_twoSidedSubexponentialBounds_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧ PlusXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
-- imply
  PlusSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalCorrelationLengthBridge_of_twoSidedSubexponentialBounds h

/--
[freeSubcriticalCorrelationLengthBridge_of_twoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalCorrelationLengthBridge_of_twoSidedSubexponentialBounds_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧ FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
-- imply
  FreeSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalCorrelationLengthBridge_of_twoSidedSubexponentialBounds h

/--
[plusSubcriticalCorrelationLengthBridge_of_fkConnectionExactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalCorrelationLengthBridge_of_fkConnectionExactExponential_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn : ℕ → ℝ) (A m : ℝ), 0 < A ∧ 0 < m ∧ PlusXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionExactExponentialDecay conn A m) :
-- imply
  PlusSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalCorrelationLengthBridge_of_fkConnectionExactExponential h

/--
[freeSubcriticalCorrelationLengthBridge_of_fkConnectionExactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalCorrelationLengthBridge_of_fkConnectionExactExponential_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn : ℕ → ℝ) (A m : ℝ), 0 < A ∧ 0 < m ∧ FreeXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionExactExponentialDecay conn A m) :
-- imply
  FreeSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalCorrelationLengthBridge_of_fkConnectionExactExponential h

/--
[plusSubcriticalCorrelationLengthBridge_of_fkConnectionSubexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalCorrelationLengthBridge_of_fkConnectionSubexponentialPrefactor_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn A : ℕ → ℝ) (m : ℝ), 0 < m ∧ PlusXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
-- imply
  PlusSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalCorrelationLengthBridge_of_fkConnectionSubexponentialPrefactor h

/--
[freeSubcriticalCorrelationLengthBridge_of_fkConnectionSubexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalCorrelationLengthBridge_of_fkConnectionSubexponentialPrefactor_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn A : ℕ → ℝ) (m : ℝ), 0 < m ∧ FreeXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
-- imply
  FreeSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalCorrelationLengthBridge_of_fkConnectionSubexponentialPrefactor h

/--
[plusSubcriticalCorrelationLengthBridge_of_fkConnectionTwoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalCorrelationLengthBridge_of_fkConnectionTwoSidedSubexponentialBounds_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧ PlusXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
-- imply
  PlusSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalCorrelationLengthBridge_of_fkConnectionTwoSidedSubexponentialBounds h

/--
[freeSubcriticalCorrelationLengthBridge_of_fkConnectionTwoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalCorrelationLengthBridge_of_fkConnectionTwoSidedSubexponentialBounds_eq
-- given
  (h : ∀ β, β < Ising.betaC 3 → ∃ (conn Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧ FreeXAxisFKConnectionAgrees β conn ∧ FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
-- imply
  FreeSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalCorrelationLengthBridge_of_fkConnectionTwoSidedSubexponentialBounds h

/--
[plusSubcriticalCorrelationLengthBridge_of_free_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalCorrelationLengthBridge_of_free_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeSubcriticalCorrelationLengthBridge) :
-- imply
  PlusSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalCorrelationLengthBridge_of_free_and_agree hagree hfree

/--
[freeSubcriticalCorrelationLengthBridge_of_plus_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalCorrelationLengthBridge_of_plus_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hplus : PlusSubcriticalCorrelationLengthBridge) :
-- imply
  FreeSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalCorrelationLengthBridge_of_plus_and_agree hagree hplus

/--
[subcriticalCorrelationLengthBridge_plus_free_agree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma subcriticalCorrelationLengthBridge_plus_free_agree_iff_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
-- imply
  PlusSubcriticalCorrelationLengthBridge ↔ FreeSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.subcriticalCorrelationLengthBridge_plus_free_agree_iff hagree

/--
[plusPositiveSubcriticalCorrelationLengthBridge_of_free_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusPositiveSubcriticalCorrelationLengthBridge_of_free_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreePositiveSubcriticalCorrelationLengthBridge) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusPositiveSubcriticalCorrelationLengthBridge_of_free_and_agree hagree hfree

/--
[freePositiveSubcriticalCorrelationLengthBridge_of_plus_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freePositiveSubcriticalCorrelationLengthBridge_of_plus_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hplus : PlusPositiveSubcriticalCorrelationLengthBridge) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freePositiveSubcriticalCorrelationLengthBridge_of_plus_and_agree hagree hplus

/--
[positiveSubcriticalCorrelationLengthBridge_plus_free_agree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma positiveSubcriticalCorrelationLengthBridge_plus_free_agree_iff_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge ↔ FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.positiveSubcriticalCorrelationLengthBridge_plus_free_agree_iff hagree

/--
[plusSubcriticalCorrelationLengthBridge_of_freeMassBridge_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusSubcriticalCorrelationLengthBridge_of_freeMassBridge_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeSubcriticalMassBridge) :
-- imply
  PlusSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusSubcriticalCorrelationLengthBridge_of_freeMassBridge_and_agree hagree hfree

/--
[freeSubcriticalCorrelationLengthBridge_of_plusMassBridge_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freeSubcriticalCorrelationLengthBridge_of_plusMassBridge_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hplus : PlusSubcriticalMassBridge) :
-- imply
  FreeSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freeSubcriticalCorrelationLengthBridge_of_plusMassBridge_and_agree hagree hplus

/--
[plusPositiveSubcriticalCorrelationLengthBridge_of_freeMassBridge_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma plusPositiveSubcriticalCorrelationLengthBridge_of_freeMassBridge_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreePositiveSubcriticalMassBridge) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.plusPositiveSubcriticalCorrelationLengthBridge_of_freeMassBridge_and_agree hagree hfree

/--
[freePositiveSubcriticalCorrelationLengthBridge_of_plusMassBridge_and_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean)
-/
@[path]
private lemma freePositiveSubcriticalCorrelationLengthBridge_of_plusMassBridge_and_agree_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hplus : PlusPositiveSubcriticalMassBridge) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.Exact3D.freePositiveSubcriticalCorrelationLengthBridge_of_plusMassBridge_and_agree hagree hplus


-- created on 2026-10-23
