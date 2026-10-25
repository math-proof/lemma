/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/FiniteGroupConvolution.lean -/


import Def.GroupTheory.FiniteGroupConvolution
import Lemma.Complex.Conv_Conv
open scoped BigOperators

open MathlibExt.GroupTheory.FiniteGroupConvolutionWanted


-- On an abelian group, the delta at one is also a right identity.
example {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (f : G → ℂ) :
    conv f (Pi.single (1 : G) (1 : ℂ)) = f := by
  calc
    conv f (Pi.single (1 : G) (1 : ℂ)) = conv (Pi.single 1 1) f :=
      conv_comm_of_comm _ _
    _ = f := conv_single_one f

-- Pairing with the trivial character makes total mass multiplicative.
example {G : Type*} [Group G] [Fintype G] (f g : G → ℂ) :
    (∑ x : G, conv f g x) = (∑ x : G, f x) * (∑ x : G, g x) := by
  simpa using charPair_conv (1 : G →* ℂ) f g

