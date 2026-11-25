module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIntegralIndependent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartIndependent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartLocal
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartSplit
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IntegralIndep.closed : IntegralIndep.Statement :=
  IntegralIndep.proof
    (PosPartIndep.proof
      (SheetOnlyNull.proof IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof
        IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof)
      PosPartLocal.proof PosPartSplit.proof)

end GroundTheory.Heights₂.Heights
