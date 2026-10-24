import sympy.analysis.Section_3_3
import Lemma.Nat.P333a.Unique
import Lemma.Set.P333c.Unique
import Lemma.Nat.P335.Unique

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
