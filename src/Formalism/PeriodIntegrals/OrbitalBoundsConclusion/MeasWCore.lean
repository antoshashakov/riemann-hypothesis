module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem weil_measure_compat : Formalism.L2.SG.Pf.MeasCore.MWCore :=
  PI.UnitaryGroupMassFormula.MeasWCore.measWCore_main
