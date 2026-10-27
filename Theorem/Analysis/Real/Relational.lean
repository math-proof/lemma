import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.InvDiv.eq.Div
import Lemma.Rat.MulDivS.eq.Div.of.Ne_0
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.StInv.eq.Inv.of.EqSt
import Lemma.Hyperreal.Infinitesimal0
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalSubDiv.Infinitesimal
import Lemma.Nat.NotLt.is.Ge
import Instance.Analysis.Real.Relational
open Hyperreal Rat Nat Int


@[symm]
theorem HasEquiv.Equiv.symm [XEq α] {a b : α} (h : a ≈ b) : b ≈ a := XEq.symm h

theorem HasEquiv.Equiv.trans [XEq α] {a b c : α} (h_ab : a ≈ b) (h_bc : b ≈ c) : a ≈ c := XEq.trans h_ab h_bc

theorem Not.XEq.symm [XEq α] {a b : α} (h : ¬a ≈ b) : ¬b ≈ a := fun h' => h h'.symm

