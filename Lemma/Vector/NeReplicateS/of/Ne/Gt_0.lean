import Lemma.Vector.EqGetS.of.Eq
open Vector


@[main]
private lemma main
-- given
  (hn : n > 0)
  (h : x ≠ y) :
-- imply
  List.Vector.replicate n x ≠ List.Vector.replicate n y := by
-- proof
  intro h_eq
  have h_head := EqGetS.of.Eq.fin h_eq ⟨0, hn⟩
  simp at h_head
  simp_all


-- created on 2025-09-23
