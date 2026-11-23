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
public import Instance.Analysis.Real.Relational
open Hyperreal Rat Nat Int

public section

@[symm]
theorem HasEquiv.Equiv.symm [XEq α] {a b : α} (h : a ≈ b) : b ≈ a := XEq.symm h

theorem HasEquiv.Equiv.trans [XEq α] {a b c : α} (h_ab : a ≈ b) (h_bc : b ≈ c) : a ≈ c := XEq.trans h_ab h_bc

theorem Not.XEq.symm [XEq α] {a b : α} (h : ¬a ≈ b) : ¬b ≈ a := fun h' => h h'.symm

