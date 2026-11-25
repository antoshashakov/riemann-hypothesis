module

public import Formalism.PeriodIntegrals.DiffGenLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDifferentGenerators.DiffExistsMain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem diffExists {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : PI.DiffGenLoc.DiffExists v :=
  PI.DiffGenLoc.UnitaryGroupMassFormula.diffExists_main v
