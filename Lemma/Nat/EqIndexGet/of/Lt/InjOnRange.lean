import sympy.tensor.index_of
import sympy.Basic
open IndexOf


@[main]
private lemma main
  [DecidableEq α]
  {j : ℕ}
-- given
  (x : ℕ → α)
  (n : ℕ)
  (hx : Set.InjOn x ↑(Finset.range n))
  (hj : j < n) :
-- imply
  index (x j) x n = j := by
-- proof
  have hnd : ((List.range n).map x).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => hx (Finset.mem_coe.mpr (Finset.mem_range.mpr (List.mem_range.mp ha)))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (List.mem_range.mp hb))) e) List.nodup_range
  have hlen : j < ((List.range n).map x).length := by simpa using hj
  simpa [index] using hnd.idxOf_getElem j hlen


-- created on 2026-10-07
