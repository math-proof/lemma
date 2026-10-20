import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.MacMahonMultiplicityOneFree
open scoped PowerSeries.WithPiTopology
open MetaMathlibExt


/--
[macmahon_multiplicity_one_free](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MacMahonMultiplicityOneFree.lean)
-/
@[path]
private lemma macmahon_multiplicity_one_free_eq
  {n : ℕ} :
-- imply
  (Finset.univ.filter (fun p : Nat.Partition n =>
    ∀ m ∈ p.parts, Multiset.count m p.parts ≠ 1)).card =
    (Nat.Partition.restricted n (fun m => m % 2 = 0 ∨ m % 6 = 3)).card := by
-- proof
  apply MetaMathlibExt.macmahon_multiplicity_one_free n


-- created on 2026-10-20
