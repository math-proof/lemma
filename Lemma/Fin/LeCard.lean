import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.SphericalBuilding.FinsetGapCorrespondenceProof.Part2
open GLnBuilding


/--
[finset_card_le_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma finset_card_le_n_eq
  {n : ℕ}
  {S : Finset (Fin n)} :
-- imply
  S.card ≤ n := by
-- proof
  apply GLnBuilding.finset_card_le_n S

/--
[finset_card_sdiff_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma finset_card_sdiff_sub_eq
  {n : ℕ}
  {lower upper : Finset (Fin n)}
-- given
  (hsub : lower ⊆ upper) :
-- imply
  (upper \ lower).card = upper.card - lower.card := by
-- proof
  apply GLnBuilding.finset_card_sdiff_sub hsub

/--
[chain_card_ge_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma chain_card_ge_succ_eq
  {n : ℕ}
  {chain : List (Finset (Fin n))}
  {i : ℕ}
-- given
  (hpw : chain.Pairwise (· ⊂ ·))
  (hne : ∀ S ∈ chain, S.Nonempty)
  (hi : i < chain.length) :
-- imply
  i + 1 ≤ (chain[i]).card := by
-- proof
  apply GLnBuilding.chain_card_ge_succ hpw hne i hi

/--
[gap_filler_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma gap_filler_core_eq
  {n : ℕ}
  {lower upper : Finset (Fin n)}
-- given
  (hsub : lower ⊆ upper)
  (hcard : 2 ≤ (upper \ lower).card) :
-- imply
  ∃ T₁ T₂ : Finset (Fin n), T₁ ≠ T₂ ∧ T₁.Nonempty ∧ T₁ ≠ Finset.univ ∧ T₂.Nonempty ∧ T₂ ≠ Finset.univ ∧ lower ⊂ T₁ ∧ T₁ ⊂ upper ∧ lower ⊂ T₂ ∧ T₂ ⊂ upper := by
-- proof
  apply GLnBuilding.gap_filler_core lower upper hsub hcard

/--
[chain_elem_subset_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma chain_elem_subset_of_lt_eq
  {n : ℕ}
  {chain : List (Finset (Fin n))}
  {bound j : ℕ}
-- given
  (hpw : chain.Pairwise (· ⊂ ·))
  (hj : j < chain.length)
  (hbound : bound < chain.length)
  (hjb : j ≤ bound) :
-- imply
  chain[j] ⊆ chain[bound] := by
-- proof
  apply GLnBuilding.chain_elem_subset_of_lt hpw hj hbound hjb

/--
[extractFinset_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma extractFinset_spec_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {F : Frame k n}
  {V : Submodule k (Vec k n)}
-- given
  (hcompat : F.IsCompatible k n V) :
-- imply
  V = ⨆ i ∈ extractFinset k n F V, F.lines i := by
-- proof
  apply GLnBuilding.extractFinset_spec k n F V hcompat

/--
[biSup_subset_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma biSup_subset_le_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {F : Frame k n}
  {S₁ S₂ : Finset (Fin n)}
-- given
  (h : S₁ ⊆ S₂) :
-- imply
  (⨆ i ∈ S₁, F.lines i) ≤ (⨆ i ∈ S₂, F.lines i) := by
-- proof
  apply GLnBuilding.biSup_subset_le k n F S₁ S₂ h

/--
[frame_line_not_le_biSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma frame_line_not_le_biSup_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {F : Frame k n}
  {S₁ : Finset (Fin n)}
  {j : Fin n}
-- given
  (hj : j ∉ S₁) :
-- imply
  ¬(F.lines j ≤ ⨆ i ∈ S₁, F.lines i) := by
-- proof
  apply GLnBuilding.frame_line_not_le_biSup k n F S₁ hj

/--
[frame_biSup_ssubset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma frame_biSup_ssubset_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {F : Frame k n}
  {S₁ S₂ : Finset (Fin n)}
-- given
  (h : S₁ ⊂ S₂) :
-- imply
  (⨆ i ∈ S₁, F.lines i) < (⨆ i ∈ S₂, F.lines i) := by
-- proof
  apply GLnBuilding.frame_biSup_ssubset k n F h

/--
[frame_biSup_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma frame_biSup_ne_bot_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {F : Frame k n}
  {S : Finset (Fin n)}
-- given
  (hne : S.Nonempty) :
-- imply
  (⨆ i ∈ S, F.lines i) ≠ ⊥ := by
-- proof
  apply GLnBuilding.frame_biSup_ne_bot k n F hne

/--
[frame_biSup_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma frame_biSup_ne_top_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {F : Frame k n}
  {S : Finset (Fin n)}
-- given
  (hne : S ≠ Finset.univ) :
-- imply
  (⨆ i ∈ S, F.lines i) ≠ ⊤ := by
-- proof
  apply GLnBuilding.frame_biSup_ne_top k n F hne

/--
[frame_biSup_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean)
-/
@[path]
private lemma frame_biSup_injective_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {F : Frame k n}
  {S₁ S₂ : Finset (Fin n)}
-- given
  (hne : S₁ ≠ S₂) :
-- imply
  (⨆ i ∈ S₁, F.lines i) ≠ (⨆ i ∈ S₂, F.lines i) := by
-- proof
  apply GLnBuilding.frame_biSup_injective k n F hne


-- created on 2026-10-23
