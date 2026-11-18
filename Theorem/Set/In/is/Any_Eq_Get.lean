module

public import Initialize.Tactic.Attr.Basic

public section


@[comm, mp, mpr]
public theorem Set.In.is.Any_Eq_Get
-- given
  (x : α)
  (s : List α):
-- imply
  x ∈ s ↔ ∃ i : Fin s.length, x = s[i] := by
-- proof
  rw [List.mem_iff_get]
  simp [Eq.comm]


public theorem Set.Any_Eq_Get.of.In
  {x : α} {s : List α}
  (h : x ∈ s) :
  ∃ i : Fin s.length, x = s[i] :=
  (Set.In.is.Any_Eq_Get x s).mp h

public theorem Set.In.of.Any_Eq_Get
  {x : α} {s : List α}
  (h : ∃ i : Fin s.length, x = s[i]) :
  x ∈ s :=
  (Set.In.is.Any_Eq_Get x s).mpr h

-- created on 2025-06-14
