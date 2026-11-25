module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocalOfFam
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FamilyMeetHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfLocal
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.L2.SG.Pf.Cnt

theorem glueExists_of (hloc : Formalism.L2.SG.Pf.G7.GlueLocal) : GlueExists :=
  Formalism.L2.SG.Pf.G7.glueExists_of_local hloc

theorem glueExists_of_fam (hJ : JordanExists) (hV : Formalism.L2.SG.Pf.GluingBases.GlueVecs)
    (h0 : Formalism.L2.SG.Pf.GluingBases.FamTop) (h1 : Formalism.L2.SG.Pf.GluingBases.FamGram) (h2 : Formalism.L2.SG.Pf.GluingBases.FamDual) :
    GlueExists :=
  glueExists_of (Formalism.L2.SG.Pf.GluingBases.glueLocal_of_fam hJ hV h0 h1 h2 Formalism.L2.SG.Pf.FamilyMeetLattice.family_meet_holds)

end Formalism.L2.SG.Pf.Cnt
