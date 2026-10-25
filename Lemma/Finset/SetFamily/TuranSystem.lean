import Mathlib
import sympy.Basic
import Def.Combinatorics.SetFamily.TuranSystem
open TuranSystem


namespace TuranSystem

/--
[pos_of_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma pos_of_isTuran
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (h : IsTuranSystem n s r H) :
-- imply
  0 < r :=
-- proof
  h.1

end TuranSystem

namespace TuranSystem

/--
[lt_of_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma lt_of_isTuran
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (h : IsTuranSystem n s r H) :
-- imply
  r < s :=
-- proof
  h.2.1

end TuranSystem

namespace TuranSystem

/--
[le_of_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma le_of_isTuran
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (h : IsTuranSystem n s r H) :
-- imply
  s ≤ n :=
-- proof
  h.2.2.1

end TuranSystem

namespace TuranSystem

/--
[uniform_of_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma uniform_of_isTuran
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (h : IsTuranSystem n s r H) :
-- imply
  SetFamily.IsUniform H r :=
-- proof
  h.2.2.2.1

end TuranSystem

namespace TuranSystem

/--
[cover_of_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma cover_of_isTuran
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (h : IsTuranSystem n s r H) :
-- imply
  ∀ T ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
    ∃ e ∈ H, e ⊆ T :=
-- proof
  h.2.2.2.2

end TuranSystem

namespace TuranSystem

/--
[completeGraph_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma completeGraph_uniform
  {n r : ℕ} :
-- imply
  SetFamily.IsUniform (completeGraph n r) r := by
-- proof
  intro e he
  exact (Finset.mem_powersetCard.mp he).2

end TuranSystem

namespace TuranSystem

/--
[completeGraph_isTuran](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma completeGraph_isTuran
  {n s r : ℕ}
-- given
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  IsTuranSystem n s r (completeGraph n r) := by
-- proof
  refine ⟨hd.1, hd.2.1, hd.2.2, completeGraph_uniform n r, ?_⟩
  intro T hT
  have hTs : T.card = s := (Finset.mem_powersetCard.mp hT).2
  have hle : r ≤ T.card := by rw [hTs]; exact Nat.le_of_lt hd.2.1
  obtain ⟨S, hST, hSc⟩ := Finset.exists_subset_card_eq hle
  exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hSc⟩, hST⟩

end TuranSystem

namespace TuranSystem

/--
[mem_realizedCounts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma mem_realizedCounts
  {n s r k : ℕ} :
-- imply
  k ∈ realizedCounts n s r ↔ ∃ H, IsTuranSystem n s r H ∧ H.card = k :=
-- proof
  Iff.rfl

end TuranSystem

namespace TuranSystem

/--
[exists_system](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma exists_system
  {n s r : ℕ}
-- given
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  ∃ H, IsTuranSystem n s r H :=
-- proof
  ⟨_, completeGraph_isTuran n s r hd⟩

end TuranSystem

namespace TuranSystem

/--
[realizedCounts_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma realizedCounts_nonempty
  {n s r : ℕ}
-- given
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  ∃ k, k ∈ realizedCounts n s r :=
-- proof
  ⟨_, _, completeGraph_isTuran n s r hd, rfl⟩

end TuranSystem

namespace TuranSystem

/--
[turanNumber_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma turanNumber_mem
  {n s r : ℕ}
-- given
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  turanNumber n s r ∈ realizedCounts n s r := by
-- proof
  classical
  have hex : ∃ k, k ∈ realizedCounts n s r := realizedCounts_nonempty n s r hd
  rw [turanNumber, dite_eq_left hex]
  exact Nat.find_spec hex

end TuranSystem

namespace TuranSystem

/--
[turanNumber_attains](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma turanNumber_attains
  {n s r : ℕ}
-- given
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  ∃ H, IsTuranSystem n s r H ∧ H.card = turanNumber n s r := by
-- proof
  obtain ⟨H, hH, hcard⟩ := turanNumber_mem n s r hd
  exact ⟨H, hH, hcard⟩

end TuranSystem

namespace TuranSystem

/--
[turanNumber_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma turanNumber_le
  {n s r : ℕ}
  {H : Finset (Finset (Fin n))}
-- given
  (hH : IsTuranSystem n s r H) :
-- imply
  turanNumber n s r ≤ H.card := by
-- proof
  classical
  have hex : ∃ k, k ∈ realizedCounts n s r := ⟨_, _, hH, rfl⟩
  rw [turanNumber, dite_eq_left hex]
  exact Nat.find_min' hex ⟨H, hH, rfl⟩

end TuranSystem

namespace TuranSystem

/--
[le_turanNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma le_turanNumber
  {n s r b : ℕ}
-- given
  (hb : ∀ k ∈ realizedCounts n s r, b ≤ k)
  (hd : 0 < r ∧ r < s ∧ s ≤ n) :
-- imply
  b ≤ turanNumber n s r :=
-- proof
  hb _ (turanNumber_mem n s r hd)

end TuranSystem


-- created on 2026-10-20
-- updated on 2026-10-23
