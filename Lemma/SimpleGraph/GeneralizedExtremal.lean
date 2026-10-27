import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.SimpleGraph.GeneralizedExtremal
open SimpleGraph


namespace SimpleGraph

/--
[generalizedExtremalNumber_eq_sup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
lemma generalizedExtremalNumber_eq_sup
  [Fintype α]
  {n : ℕ}
  {T : SimpleGraph α}
  {H : SimpleGraph β} :
-- imply
  generalizedExtremalNumber n T H =
    Finset.sup (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
    (fun G => G.copyCount T) := by
-- proof
  classical
  unfold generalizedExtremalNumber
  rfl

end SimpleGraph

namespace SimpleGraph

/--
[copyCount_le_generalizedExtremalNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
lemma copyCount_le_generalizedExtremalNumber
  [Fintype α]
  {n : ℕ}
  {T : SimpleGraph α}
  {H : SimpleGraph β}
  {G : SimpleGraph (Fin n)}
-- given
  (hG : H.Free G) :
-- imply
  G.copyCount T ≤ generalizedExtremalNumber n T H := by
-- proof
  classical
  unfold generalizedExtremalNumber
  apply Finset.le_sup (s := Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
    (f := fun G => G.copyCount T) (b := G)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩

end SimpleGraph

namespace SimpleGraph

/--
[generalizedExtremalNumber_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
lemma generalizedExtremalNumber_le_iff
  [Fintype α]
  {n : ℕ}
  {T : SimpleGraph α}
  {H : SimpleGraph β}
  {m : ℕ} :
-- imply
  generalizedExtremalNumber n T H ≤ m ↔
    ∀ G : SimpleGraph (Fin n), H.Free G → G.copyCount T ≤ m := by
-- proof
  classical
  unfold generalizedExtremalNumber
  rw [Finset.sup_le_iff]
  constructor
  · intro h G hG
    exact h _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩)
  · intro h b hb
    exact h b (Finset.mem_filter.mp hb).2

end SimpleGraph

namespace SimpleGraph

/--
[exists_free_copyCount_eq_generalizedExtremalNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
lemma exists_free_copyCount_eq_generalizedExtremalNumber
  [Fintype α]
  {n : ℕ}
  {T : SimpleGraph α}
  {H : SimpleGraph β}
-- given
  (hne : ∃ G : SimpleGraph (Fin n), H.Free G) :
-- imply
  ∃ G : SimpleGraph (Fin n), H.Free G ∧ G.copyCount T = generalizedExtremalNumber n T H := by
-- proof
  classical
  have hne' : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G)).Nonempty := by
    obtain ⟨G0, hG0⟩ := hne
    exact ⟨G0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG0⟩⟩
  have hEx : ∃ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G),
    Finset.sup
      (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
      (fun G => G.copyCount T) = G.copyCount T :=
    Finset.exists_mem_eq_sup
      (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G)) hne'
      (fun G => G.copyCount T)
  obtain ⟨G, hGmem, hEq⟩ := hEx
  have hFree : H.Free G := (Finset.mem_filter.mp hGmem).2
  have hdef := generalizedExtremalNumber_eq_sup n T H
  exact ⟨G, hFree, hEq.symm.trans hdef.symm⟩

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-26
