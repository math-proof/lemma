import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SetFamily.TuranSystem
open TuranSystem


/--
[pos_of_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma pos_of_isTuran_eq
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (h : IsTuranSystem n s r H) :
-- imply
  0 < r := by
-- proof
  apply TuranSystem.pos_of_isTuran n s r H h

/--
[lt_of_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma lt_of_isTuran_eq
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (h : IsTuranSystem n s r H) :
-- imply
  r < s := by
-- proof
  apply TuranSystem.lt_of_isTuran n s r H h

/--
[le_of_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma le_of_isTuran_eq
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (h : IsTuranSystem n s r H) :
-- imply
  s ≤ n := by
-- proof
  apply TuranSystem.le_of_isTuran n s r H h

/--
[uniform_of_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma uniform_of_isTuran_eq
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (h : IsTuranSystem n s r H) :
-- imply
  SetFamily.IsUniform H r := by
-- proof
  apply TuranSystem.uniform_of_isTuran n s r H h

/--
[cover_of_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma cover_of_isTuran_eq
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (h : IsTuranSystem n s r H) :
-- imply
  ∀ T ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
    ∃ e ∈ H, e ⊆ T := by
-- proof
  apply TuranSystem.cover_of_isTuran n s r H h

/--
[completeGraph_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma completeGraph_uniform_eq
  {n r : ℕ} :
-- imply
  SetFamily.IsUniform (completeGraph n r) r := by
-- proof
  apply TuranSystem.completeGraph_uniform n r

/--
[completeGraph_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma completeGraph_isTuran_eq
  {n s r : ℕ}
-- given
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  IsTuranSystem n s r (completeGraph n r) := by
-- proof
  apply TuranSystem.completeGraph_isTuran n s r hd

/--
[mem_realizedCounts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma mem_realizedCounts_eq
  {n s r k : ℕ} :
-- imply
  k ∈ realizedCounts n s r ↔ ∃ H, IsTuranSystem n s r H ∧ H.card = k := by
-- proof
  apply TuranSystem.mem_realizedCounts n s r k

/--
[exists_system](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma exists_system_eq
  {n s r : ℕ}
-- given
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  ∃ H, IsTuranSystem n s r H := by
-- proof
  apply TuranSystem.exists_system n s r hd

/--
[realizedCounts_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma realizedCounts_nonempty_eq
  {n s r : ℕ}
-- given
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  ∃ k, k ∈ realizedCounts n s r := by
-- proof
  apply TuranSystem.realizedCounts_nonempty n s r hd

/--
[turanNumber_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma turanNumber_mem_eq
  {n s r : ℕ}
-- given
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  turanNumber n s r ∈ realizedCounts n s r := by
-- proof
  apply TuranSystem.turanNumber_mem n s r hd

/--
[turanNumber_attains](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma turanNumber_attains_eq
  {n s r : ℕ}
-- given
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  ∃ H, IsTuranSystem n s r H ∧ H.card = turanNumber n s r := by
-- proof
  apply TuranSystem.turanNumber_attains n s r hd

/--
[turanNumber_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma turanNumber_le_eq
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (hH : IsTuranSystem n s r H) :
-- imply
  turanNumber n s r ≤ H.card := by
-- proof
  apply TuranSystem.turanNumber_le n s r H hH

/--
[le_turanNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
private lemma le_turanNumber_eq
  {n s r b : ℕ}
-- given
  (hb : ∀ k ∈ realizedCounts n s r, b ≤ k)
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  b ≤ turanNumber n s r := by
-- proof
  apply TuranSystem.le_turanNumber n s r b hb hd


-- created on 2026-10-20
