module

public import Formalism.QuotientMetricDivisors.DivIntoDualShift
public import Formalism.QuotientMetricDivisors.HeightBoundExactNorms
public import Formalism.QuotientMetricDivisors.LatticeGlueUnique
public import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundRows
public import Formalism.QuotientMetricDivisors.TheoremDivIneqRowsShift
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DescendedNorm
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TwistedLatticeNaturality
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.WeightedPlaceLogSum
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramHook
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramTopExact
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.DivisionValues

theorem latticeGlue : LatticeGlue := lattice_gluing

theorem height_constant_bound : HeightBoundConstant := height_constant_first

theorem rowsHook : RowsHook := young_diagram_hook

theorem rowsStepEOrigin : RowsStepEOrigin := young_diagram_step_origin

theorem shiftMu : ShiftMu := by
  unfold ShiftMu
  exact shift_slope_mu

theorem shiftEx : ShiftEx := by
  unfold ShiftEx
  exact shift_existence

theorem divIntoDualShift : DivIntoDualShift := divisor_into_dual_shift

theorem primeLogSum : PrimeLogSum := prime_log_sum_bound

end Formalism.DivisionValues
