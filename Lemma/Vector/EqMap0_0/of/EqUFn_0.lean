import sympy.vector.Basic
import Lemma.Vector.Zero.eq.Replicate


@[main]
private lemma main
  [Zero γ] [Zero δ]
-- given
  (f : γ → δ) (hf : f 0 = 0) :
-- imply
  (0 : List.Vector γ n).map f = 0 := by
-- proof
  have hmap : (0 : List.Vector γ n).map f = List.Vector.replicate n (f 0) := by
    rw [← Vector.Replicate.eq.Zero]
    apply Subtype.ext
    simp [List.Vector.map, List.Vector.replicate, List.map_replicate]
  rw [hmap, hf, Vector.Replicate.eq.Zero]


-- created on 2026-09-15
