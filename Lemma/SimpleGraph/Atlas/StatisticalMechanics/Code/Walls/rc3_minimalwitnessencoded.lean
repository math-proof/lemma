import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc3_minimalwitnessencoded
open Finset StatMech StatMech.Walls


/--
[cylinder_supportCfg_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_minimalwitnessencoded.lean)
-/
@[path]
private lemma cylinder_supportCfg_of_support_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s : Finset E}
  {K : Finset E}
-- given
  (hs : s = cfgSupport ω) :
-- imply
  cylinder K (supportCfg s) = cylinder K ω := by
-- proof
  apply StatMech.Walls.cylinder_supportCfg_of_support hs K

/--
[mem_cylinder_supportCfg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_minimalwitnessencoded.lean)
-/
@[path]
private lemma mem_cylinder_supportCfg_iff_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s : Finset E}
  {K : Finset E}
  {ω' : ConfigSpace E}
-- given
  (hs : s = cfgSupport ω) :
-- imply
  ω' ∈ cylinder K (supportCfg s) ↔ cfgSupport ω' ∩ K = s ∩ K := by
-- proof
  apply StatMech.Walls.mem_cylinder_supportCfg_iff hs K ω'

/--
[mem_of_supportEncoding_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_minimalwitnessencoded.lean)
-/
@[path]
private lemma mem_of_supportEncoding_decode_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L : Finset E}
-- given
  (h : SupportEncodedMinimalWitness A B ω s K L) :
-- imply
  cylinder K (supportCfg s) ⊆ A ∧ cylinder L (supportCfg s) ⊆ B := by
-- proof
  apply StatMech.Walls.mem_of_supportEncoding_decode h

/--
[exists_supportEncodedMinimalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_minimalwitnessencoded.lean)
-/
@[path]
private lemma exists_supportEncodedMinimalWitness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  ∃ s K L : Finset E, SupportEncodedMinimalWitness A B ω s K L := by
-- proof
  apply StatMech.Walls.exists_supportEncodedMinimalWitness hω

/--
[mem_of_supportEncodedMinimalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_minimalwitnessencoded.lean)
-/
@[path]
private lemma mem_of_supportEncodedMinimalWitness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L : Finset E}
-- given
  (h : SupportEncodedMinimalWitness A B ω s K L) :
-- imply
  ω ∈ disjointOccurrence A B := by
-- proof
  apply StatMech.Walls.mem_of_supportEncodedMinimalWitness h

/--
[mem_disjointOccurrence_iff_supportEncodedMinimalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_minimalwitnessencoded.lean)
-/
@[path]
private lemma mem_disjointOccurrence_iff_supportEncodedMinimalWitness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  ω ∈ disjointOccurrence A B ↔ ∃ s K L : Finset E, SupportEncodedMinimalWitness A B ω s K L := by
-- proof
  apply StatMech.Walls.mem_disjointOccurrence_iff_supportEncodedMinimalWitness

/--
[supportCfg_of_supportEncodedMinimalWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_minimalwitnessencoded.lean)
-/
@[path]
private lemma supportCfg_of_supportEncodedMinimalWitness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L : Finset E}
-- given
  (h : SupportEncodedMinimalWitness A B ω s K L) :
-- imply
  supportCfg s = ω := by
-- proof
  apply StatMech.Walls.supportCfg_of_supportEncodedMinimalWitness h

/--
[support_eq_cfgEquivFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_minimalwitnessencoded.lean)
-/
@[path]
private lemma support_eq_cfgEquivFinset_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {s K L : Finset E}
-- given
  (h : SupportEncodedMinimalWitness A B ω s K L) :
-- imply
  s = cfgEquivFinset ω := by
-- proof
  apply StatMech.Walls.support_eq_cfgEquivFinset h

/--
[exists_supportEncodedMinimalWitness_of_disjoint_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_minimalwitnessencoded.lean)
-/
@[path]
private lemma exists_supportEncodedMinimalWitness_of_disjoint_witness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {K L : Finset E}
-- given
  (hKL : Disjoint K L)
  (hA : cylinder K ω ⊆ A)
  (hB : cylinder L ω ⊆ B) :
-- imply
  ∃ s K' L' : Finset E, SupportEncodedMinimalWitness A B ω s K' L' := by
-- proof
  apply StatMech.Walls.exists_supportEncodedMinimalWitness_of_disjoint_witness hKL hA hB


-- created on 2026-10-23
