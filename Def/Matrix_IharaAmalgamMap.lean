import Def.Matrix_IharaAmalgam
import Def.Matrix_Main

namespace Ihara

open Matrix CongruenceSubgroup

open scoped MatrixGroups

variable (N q : ℕ)

def slToAway : SL(2, ℤ) →* SL(2, ZAway q) :=
  Matrix.SpecialLinearGroup.map (algebraMap ℤ (ZAway q))

def vertexZero : Gamma0 N →* SL(2, ZAway q) :=
  (slToAway q).comp (Gamma0 N).subtype

noncomputable def vertexOne : Gamma0 N →* SL(2, ZAway q) :=
  (wConj q).symm.toMonoidHom.comp (vertexZero N q)

noncomputable def amalgamToAway : iharaAmalgam N q →* SL(2, ZAway q) :=
  iharaLift (vertexZero N q) (vertexOne N q) (vertex_compat N q)

noncomputable def amalgamToGamma0Away : iharaAmalgam N q →* Gamma0Away N q :=
  (amalgamToAway N q).codRestrict (Gamma0Away N q) (amalgamToAway_mem N q)

end Ihara
