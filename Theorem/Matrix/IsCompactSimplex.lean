module
public import Theorem.Matrix.Simplex.sub.ClosedBall
open Metric Matrix


public section

@[path]
private theorem main
  {S : Type*} [Fintype S] :
-- imply
  IsCompact (Simplex S) := by
-- proof
  apply isCompact_of_isClosed_isBounded
  · infer_instance
  · exact (isBounded_iff_subset_closedBall (0 : l1Space S)).mpr ⟨1, Simplex.sub.ClosedBall⟩


-- created on 2026-09-19
-- updated on 2026-09-26
