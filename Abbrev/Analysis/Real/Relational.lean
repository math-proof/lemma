module

public import Theorem.Rat.Div.eq.One.of.Ne_0
public import Theorem.Rat.InvDiv.eq.Div
public import Theorem.Rat.MulDivS.eq.Div.of.Ne_0
public import Theorem.Hyperreal.EqSt.of.InfinitesimalSub
public import Theorem.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
public import Theorem.Hyperreal.EqSt_0.of.Infinite
public import Theorem.Hyperreal.StInv.eq.Inv.of.EqSt
public import Theorem.Hyperreal.Infinitesimal0
public import Theorem.Hyperreal.Infinitesimal.of.InfinitesimalSubDiv.Infinitesimal
public import Theorem.Nat.NotLt.is.Ge
@[expose] public section

open Hyperreal Rat Nat Int


abbrev XEq (α : Sort u) := Setoid α

namespace XEq
export Setoid (symm trans)
end XEq

