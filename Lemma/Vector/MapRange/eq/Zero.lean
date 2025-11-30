import Lemma.Vector.Replicate.eq.MapRange
import Lemma.Vector.Zero.eq.Replicate
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (n : ℕ) :
-- imply
  (List.Vector.range n).map (fun _ => 0) = (0 : List.Vector α n) := by
-- proof
  rw [Zero.eq.Replicate]
  rw [Replicate.eq.MapRange]


-- created on 2025-11-30
