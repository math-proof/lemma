module

public import Abbrev.Analysis.Section_3_3.Part2
public import Theorem.Nat.P333a.Unique
public import Theorem.Set.P333c.Unique
public import Theorem.Nat.P335.Unique

@[expose] public section


namespace Chapter3

variable [SetTheory]

open SetTheory

open SetTheory.Set

abbrev SetTheory.Set.f_3_3_3a : Function Nat Nat :=
  Function.mk P_3_3_3a (fun x ↦ _root_.Nat.P333a.Unique (x := x))

abbrev SetTheory.Set.f_3_3_3c : Function (Nat \ {(0:Object)}: Set) Nat :=
  Function.mk P_3_3_3c (fun x ↦ _root_.Set.P333c.Unique (x := x))

abbrev SetTheory.Set.f_3_3_5 : Function Nat Nat :=
  Function.mk P_3_3_5 (fun x ↦ _root_.Nat.P335.Unique (x := x))

end Chapter3
