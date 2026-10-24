import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Coloring.Vertex
open SimpleGraph


namespace SimpleGraph

/--
[lt_chromaticNumber_iff_not_colorable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
lemma lt_chromaticNumber_iff_not_colorable
  {G : SimpleGraph V}
  {n : ℕ} :
-- imply
  n < G.chromaticNumber ↔ ¬ G.Colorable n := by
-- proof
  rw [← chromaticNumber_le_iff_colorable, not_le]

end SimpleGraph

namespace SimpleGraph

/--
[le_chromaticNumber_iff_not_colorable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
lemma le_chromaticNumber_iff_not_colorable
  {G : SimpleGraph V}
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  n ≤ G.chromaticNumber ↔ ¬ G.Colorable (n - 1) := by
-- proof
  let n + 1 := n; simp [ENat.add_one_le_iff, lt_chromaticNumber_iff_not_colorable]

end SimpleGraph

namespace SimpleGraph

/--
[card_div_indepNum_le_chromaticNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
lemma card_div_indepNum_le_chromaticNumber
  {G : SimpleGraph V}
  {n : ℕ} :
-- imply
  ⌈(Nat.card V / α(G) : ℚ≥0)⌉₊ ≤ G.chromaticNumber := by
-- proof
  cases finite_or_infinite V
  swap; · simp
  cases nonempty_fintype V
  simp only [Nat.card_eq_fintype_card, le_chromaticNumber_iff_coloring, Nat.ceil_le]
  refine fun m c ↦ div_le_of_le_mul₀ (by simp) (by simp) ?_
  norm_cast
  rw [← mul_one (Fintype.card V), ← Fintype.card_fin m]
  refine Finset.card_mul_le_card_mul (c · = ·)
    (by simp [Finset.bipartiteAbove, Finset.filter_nonempty_iff])
    fun b _ ↦ IsIndepSet.card_le_indepNum ?_
  simpa [IsIndepSet, Set.Pairwise, Coloring.colorClass] using
    fun x hx y hy _ ↦ c.not_adj_of_mem_colorClass hx hy

end SimpleGraph

namespace SimpleGraph

/--
[not_isCritical_of_fintype_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
lemma not_isCritical_of_fintype_lt
  [Fintype V]
  {G : SimpleGraph V}
  {G}
  {k : ℕ}
-- given
  (hk : Fintype.card V < k) :
-- imply
  ¬G.IsCritical k := by
-- proof
  simp only [IsCritical, not_and, not_forall]
  intro h
  have := h ▸ SimpleGraph.chromaticNumber_le_iff_colorable.2 G.colorable_of_fintype
  simp at this
  grind
open SimpleGraph
set_option backward.isDefEq.respectTransparency false in

end SimpleGraph

namespace SimpleGraph

/--
[colorable_iff_induce_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
lemma colorable_iff_induce_eq_bot
  {G}
  {G : SimpleGraph V}
  {n : ℕ} :
-- imply
  G.Colorable n ↔ ∃ coloring : V → Fin n, ∀ i, G.induce {v | coloring v = i} = ⊥ := by
-- proof
  refine ⟨fun ⟨a, h⟩ ↦ ⟨a, fun i ↦ ?_⟩, fun ⟨w, h⟩ ↦ ⟨w, @fun a b h_adj ↦ ?_⟩⟩
  · rw [SimpleGraph.eq_bot_iff_forall_not_adj]
    rintro ⟨u, huv⟩ ⟨v, rfl⟩ huv'
    exact (h huv').ne huv
  specialize h (w a)
  contrapose h
  intro hG
  have : ¬ ((SimpleGraph.induce {v | w v = w a} G).Adj ⟨a, by rfl⟩ ⟨b, by simp_all⟩) :=
    hG ▸ fun a ↦ a
  exact this h_adj

end SimpleGraph

namespace SimpleGraph

/--
[Colorable.cocolorable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
lemma Colorable.cocolorable
  {G : SimpleGraph V}
  {G}
  {n : ℕ}
-- given
  (hc : G.Colorable n) :
-- imply
  G.Cocolorable n := by
-- proof
  obtain ⟨coloring, hcol⟩ := (colorable_iff_induce_eq_bot G n).mp hc
  exact ⟨coloring, fun i => Or.inl (hcol i)⟩

end SimpleGraph

namespace SimpleGraph

/--
[cocolorable_of_fintype](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
lemma cocolorable_of_fintype
  [Fintype V]
  {G}
  {G : SimpleGraph V} :
-- imply
  G.Cocolorable (Fintype.card V) :=
-- proof
  (colorable_of_fintype G).cocolorable

end SimpleGraph

namespace SimpleGraph

/--
[Cocolorable.cochromaticNumber_eq_sInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
lemma Cocolorable.cochromaticNumber_eq_sInf
  {G : SimpleGraph V}
  {G}
  {n : ℕ}
-- given
  (h : G.Cocolorable n) :
-- imply
  G.cochromaticNumber = sInf {n' : ℕ | G.Cocolorable n'} := by
-- proof
  rw [ENat.natCast_sInf, cochromaticNumber]
  exact ⟨_, h⟩

end SimpleGraph

namespace SimpleGraph

/--
[cochromaticNumber_toNat_eq_sInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
lemma cochromaticNumber_toNat_eq_sInf
  [Fintype V]
  {n : ℕ}
  {G}
  {G : SimpleGraph V} :
-- imply
  G.cochromaticNumber.toNat = sInf {n : ℕ | G.Cocolorable n} := by
-- proof
  rw [(cocolorable_of_fintype G).cochromaticNumber_eq_sInf, ENat.toNat_natCast]

end SimpleGraph

namespace SimpleGraph

/--
[indepNumK_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
lemma indepNumK_le_card
  [Fintype V]
  {G}
  {G : SimpleGraph V}
  {k : ℕ} :
-- imply
  indepNumK G k ≤ Fintype.card V := by
-- proof
  refine csSup_le ⟨0, fun _ => ∅, fun _ _ hx => False.elim hx, by simp⟩ ?_
  rintro n ⟨f, _, rfl⟩
  simpa using Set.ncard_le_card (⋃ i, f i)

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
