import Instance.MvFormalGroup_NegV2
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Finiteness.Ideal
import Instance.MvFormalGroup_PointsV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

section AdicEval

variable {S : Type*} [CommRing S] [Algebra R S] {S' : Type*} [CommRing S'] [Algebra R S']
  {σ : Type*}


open MvPowerSeries.WithPiTopology in


end AdicEval

structure Points (F : MvFormalGroup g R) (S : Type*) [CommRing S] (J : Ideal S) : Type _ where

  val : Fin g → S

  mem_radical : ∀ i, val i ∈ J.radical

namespace Points

variable {F : MvFormalGroup g R} {S : Type*} [CommRing S] {J : Ideal S}


variable [Algebra R S]


variable [IsAdicComplete J S]


end Points

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R} {H : MvFormalGroup k R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]


end Hom

namespace Points

variable {F : MvFormalGroup g R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]
  {S' : Type*} [CommRing S'] [Algebra R S'] {J' : Ideal S'} [IsAdicComplete J' S']


end Points

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]
  {S' : Type*} [CommRing S'] [Algebra R S'] {J' : Ideal S'} [IsAdicComplete J' S']


end Hom

end MvFormalGroup
