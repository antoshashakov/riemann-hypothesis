module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.DetectIdeal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.DivAtOneOfInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.ExistsConjugationFixedUniformizer
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.ExistsDenFg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.Imports
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsUnimodularOfIsSDG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsUnitIffSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SplitPlaceOf
import Supplements.MathlibImports.AnalysisAndTactics
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsMaximalComapCj

@[expose] public section

namespace PI.SqPairLocal

theorem modelEx : ModelEx := modelEx_of fixedDVR realUnif

theorem sqPairLocal_of (h : PI.SqPair.LocCartanPair) : PI.SqPair.PLocalAll :=
  sqPairLocal_of_steps h locGlob intMul (glue_of powLoc) (splitPlace_of powLoc) inertAsm modelEx dict locMat
    powLoc

end PI.SqPairLocal
