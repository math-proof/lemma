import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc4_massshiftinvariant
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc4_mass_shift_bijOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massshiftinvariant.lean)
-/
@[path]
private lemma gc4_mass_shift_bijOn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {S : Finset V}
-- given
  (hK : K ⊆ m) :
-- imply
  Set.BijOn (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = S} {N | N ⊆ m ∧ sources ends N = S ∆ sources ends K} := by
-- proof
  apply StatMech.Walls.gc4_mass_shift_bijOn ends m K hK S

/--
[gc4_aie_mass_shift_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massshiftinvariant.lean)
-/
@[path]
private lemma gc4_aie_mass_shift_invariant_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {S : Finset V}
  {φ : Finset ι → ℝ}
-- given
  (hK : K ⊆ m)
  (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
-- imply
  aie_mass ends m φ (S ∆ sources ends K) = aie_mass ends m φ S := by
-- proof
  apply StatMech.Walls.gc4_aie_mass_shift_invariant ends m K hK S φ hφ

/--
[gc4_aie_mass_shift_invariant'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massshiftinvariant.lean)
-/
@[path]
private lemma gc4_aie_mass_shift_invariant'_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {S : Finset V}
  {φ : Finset ι → ℝ}
-- given
  (hK : K ⊆ m)
  (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
-- imply
  aie_mass ends m φ S = aie_mass ends m φ (S ∆ sources ends K) := by
-- proof
  apply StatMech.Walls.gc4_aie_mass_shift_invariant' ends m K hK S φ hφ

/--
[gc4_mass_shift_invariant_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massshiftinvariant.lean)
-/
@[path]
private lemma gc4_mass_shift_invariant_pair_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {S : Finset V}
  {u v : V}
  {φ : Finset ι → ℝ}
-- given
  (hK : K ⊆ m)
  (hKsrc : sources ends K = {u, v})
  (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
-- imply
  aie_mass ends m φ (S ∆ {u, v}) = aie_mass ends m φ S := by
-- proof
  apply StatMech.Walls.gc4_mass_shift_invariant_pair ends m K hK S hKsrc φ hφ

/--
[gc4_mass_shift_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massshiftinvariant.lean)
-/
@[path]
private lemma gc4_mass_shift_empty_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {S : Finset V}
  {φ : Finset ι → ℝ}
-- given
  (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
-- imply
  aie_mass ends m φ (S ∆ sources ends (∅ : Finset ι)) = aie_mass ends m φ S := by
-- proof
  apply StatMech.Walls.gc4_mass_shift_empty ends m S φ hφ

/--
[gc4_mass_self_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massshiftinvariant.lean)
-/
@[path]
private lemma gc4_mass_self_shift_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {φ : Finset ι → ℝ}
-- given
  (hK : K ⊆ m)
  (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
-- imply
  aie_mass ends m φ (sources ends K) = aie_mass ends m φ ∅ := by
-- proof
  apply StatMech.Walls.gc4_mass_self_shift ends m K hK φ hφ


-- created on 2026-10-23
