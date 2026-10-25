/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/KuratowskiClosureComplement.lean -/

import Lemma.Set.KuratowskiClosureComplement
open Set
open Topology.ClosureCompl
open MathlibExt.Topology.KuratowskiClosureComplement


/-- Discrete topology on `Fin 2` for the concrete examples below. -/
instance : TopologicalSpace (Fin 2) where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

