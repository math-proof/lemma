module

public import Theorem.Vector.Get.of.Eq
public import Mathlib.Data.Vector.Basic

public section

open Vector


public theorem Vector.NeReplicateS.of.Ne.Gt_0
  {x y : α}
-- given
  (hn : n > 0)
  (h : x ≠ y) :
-- imply
  List.Vector.replicate n x ≠ List.Vector.replicate n y := by
-- proof
  intro h_eq
  apply h
  have h_head := congrArg (fun v : List.Vector α n => v.get ⟨0, hn⟩) h_eq
  simpa [List.Vector.get_replicate] using h_head


-- created on 2025-09-23
