import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInhom.Part2
open Finset StatMech StatMech.Sharpness


/--
[shk_pweight_splitAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInhom.lean)
-/
@[path]
private lemma shk_pweight_splitAt_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {e : E}
  {b : Bool}
-- given
  (rest : {j // j ≠ e} → Bool) :
-- imply
  pweight phi ((Equiv.piSplitAt e (fun _ : E => Bool)).symm (b, rest)) = phi e b * pweight (fun j : {j // j ≠ e} => phi j.1) rest := by
-- proof
  apply StatMech.Sharpness.shk_pweight_splitAt phi e b rest

/--
[shk_wprob_edgeOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInhom.lean)
-/
@[path]
private lemma shk_wprob_edgeOpen_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {e : E}
-- given
  (hphi : ∀ e, phi e false + phi e true = 1) :
-- imply
  wprob phi {omega : ConfigSpace E | omega e = true} = phi e true := by
-- proof
  apply StatMech.Sharpness.shk_wprob_edgeOpen phi hphi e

/--
[shk_bk_triple_inhom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInhom.lean)
-/
@[path]
private lemma shk_bk_triple_inhom_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {P Q R : Set (ConfigSpace E)}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1)
  (hP : IsIncreasing P)
  (hQ : IsIncreasing Q)
  (hR : IsIncreasing R) :
-- imply
  wprob phi (disjointOccurrence P (disjointOccurrence Q R)) ≤ wprob phi P * wprob phi Q * wprob phi R := by
-- proof
  apply StatMech.Sharpness.shk_bk_triple_inhom phi hphi0 hphi1 hP hQ hR

/--
[shk_wprob_biUnion_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInhom.lean)
-/
@[path]
private lemma shk_wprob_biUnion_le_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {s : Finset I}
  {F : I → Set (ConfigSpace E)}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b) :
-- imply
  wprob phi (⋃ i ∈ s, F i) ≤ ∑ i ∈ s, wprob phi (F i) := by
-- proof
  apply StatMech.Sharpness.shk_wprob_biUnion_le phi hphi0 s F

/--
[shk_edgeLaw_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInhom.lean)
-/
@[path]
private lemma shk_edgeLaw_nonneg_eq
  {beta : ℝ}
  {J : E → ℝ}
  {e : E}
  {b : Bool}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ shk_edgeLaw beta J e b := by
-- proof
  apply StatMech.Sharpness.shk_edgeLaw_nonneg beta J hbeta hJ e b

/--
[shk_edgeLaw_sum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInhom.lean)
-/
@[path]
private lemma shk_edgeLaw_sum_one_eq
  {beta : ℝ}
  {J : E → ℝ}
  {e : E} :
-- imply
  shk_edgeLaw beta J e false + shk_edgeLaw beta J e true = 1 := by
-- proof
  apply StatMech.Sharpness.shk_edgeLaw_sum_one beta J e

/--
[bk_criterion_inhomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInhom.lean)
-/
@[path]
private lemma bk_criterion_inhomogeneous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Set V}
  {S : Finset V}
  {B : Set V}
  {u : V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (huS : u ∈ S)
  (hBS : ∀ z ∈ B, z ∉ S) :
-- imply
  wprob (shk_edgeLaw beta J) (connEvent G A u B) ≤ ∑ q ∈ shk_boundaryPairs G S, (1 - Real.exp (-beta * J s(q.1, q.2))) * wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) u {q.1}) * wprob (shk_edgeLaw beta J) (connEvent G A q.2 B) := by
-- proof
  apply StatMech.Sharpness.bk_criterion_inhomogeneous G beta J hbeta hJ A S B u huS hBS


-- created on 2026-10-23
