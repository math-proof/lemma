import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc2_minimalwitness
open Finset StatMech StatMech.Walls


/--
[exists_minimal_witness_of_wellFounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_minimalwitness.lean)
-/
@[path]
private lemma exists_minimal_witness_of_wellFounded_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {K : Finset E}
-- given
  (hK : cylinder K ω ⊆ A) :
-- imply
  ∃ K₀ ⊆ K, Minimal (fun S => cylinder S ω ⊆ A) K₀ := by
-- proof
  apply StatMech.Walls.exists_minimal_witness_of_wellFounded hK

/--
[not_witness_of_lt_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_minimalwitness.lean)
-/
@[path]
private lemma not_witness_of_lt_minimal_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {K S : Finset E}
-- given
  (hmin : Minimal (fun S => cylinder S ω ⊆ A) K)
  (hlt : S ⊂ K) :
-- imply
  ¬ cylinder S ω ⊆ A := by
-- proof
  apply StatMech.Walls.not_witness_of_lt_minimal hmin hlt

/--
[minimal_witness_eq_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_minimalwitness.lean)
-/
@[path]
private lemma minimal_witness_eq_of_subset_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {K S : Finset E}
-- given
  (hmin : Minimal (fun S => cylinder S ω ⊆ A) K)
  (hS : cylinder S ω ⊆ A)
  (hSK : S ⊆ K) :
-- imply
  S = K := by
-- proof
  apply StatMech.Walls.minimal_witness_eq_of_subset hmin hS hSK

/--
[minimal_witness_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_minimalwitness.lean)
-/
@[path]
private lemma minimal_witness_card_le_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {K S : Finset E}
-- given
  (hmin : Minimal (fun S => cylinder S ω ⊆ A) K)
  (hS : cylinder S ω ⊆ A)
  (hSK : S ⊆ K) :
-- imply
  K.card ≤ S.card := by
-- proof
  apply StatMech.Walls.minimal_witness_card_le hmin hS hSK

/--
[exists_minimal_disjoint_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_minimalwitness.lean)
-/
@[path]
private lemma exists_minimal_disjoint_witness_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  [Finite E] :
-- imply
  ω ∈ disjointOccurrence A B ↔ ∃ K L : Finset E, Disjoint K L ∧ Minimal (fun S => cylinder S ω ⊆ A) K ∧ Minimal (fun S => cylinder S ω ⊆ B) L := by
-- proof
  apply StatMech.Walls.exists_minimal_disjoint_witness

/--
[minimal_disjoint_witness_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_minimalwitness.lean)
-/
@[path]
private lemma minimal_disjoint_witness_of_mem_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  [Finite E]
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  ∃ K L : Finset E, Disjoint K L ∧ Minimal (fun S => cylinder S ω ⊆ A) K ∧ Minimal (fun S => cylinder S ω ⊆ B) L := by
-- proof
  apply StatMech.Walls.minimal_disjoint_witness_of_mem hω

/--
[mem_of_disjoint_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_minimalwitness.lean)
-/
@[path]
private lemma mem_of_disjoint_witness_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  [Finite E]
  {K L : Finset E}
-- given
  (hKL : Disjoint K L)
  (hA : cylinder K ω ⊆ A)
  (hB : cylinder L ω ⊆ B) :
-- imply
  ω ∈ disjointOccurrence A B := by
-- proof
  apply StatMech.Walls.mem_of_disjoint_witness hKL hA hB

/--
[cylinder_eq_supportSlice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_minimalwitness.lean)
-/
@[path]
private lemma cylinder_eq_supportSlice_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  [Fintype E]
  [DecidableEq E]
  {K : Finset E}
  {ω ω' : ConfigSpace E} :
-- imply
  ω' ∈ cylinder K ω ↔ cfgSupport ω' ∩ K = cfgSupport ω ∩ K := by
-- proof
  apply StatMech.Walls.cylinder_eq_supportSlice K ω ω'

/--
[exists_support_encoded_minimal_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_minimalwitness.lean)
-/
@[path]
private lemma exists_support_encoded_minimal_witness_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  [Fintype E]
  [DecidableEq E]
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  ∃ (s K L : Finset E), s = cfgSupport ω ∧ Disjoint K L ∧ Minimal (fun S => cylinder S ω ⊆ A) K ∧ Minimal (fun S => cylinder S ω ⊆ B) L := by
-- proof
  apply StatMech.Walls.exists_support_encoded_minimal_witness hω

/--
[mem_of_support_encoding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_minimalwitness.lean)
-/
@[path]
private lemma mem_of_support_encoding_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  [Fintype E]
  [DecidableEq E]
  {s K L : Finset E}
-- given
  (hs : s = cfgSupport ω)
  (hKL : Disjoint K L)
  (hA : cylinder K (supportCfg s) ⊆ A)
  (hB : cylinder L (supportCfg s) ⊆ B) :
-- imply
  ω ∈ disjointOccurrence A B := by
-- proof
  apply StatMech.Walls.mem_of_support_encoding hs hKL hA hB


-- created on 2026-10-23
