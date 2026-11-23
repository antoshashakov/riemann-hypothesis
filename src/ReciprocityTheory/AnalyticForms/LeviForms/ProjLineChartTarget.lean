module

public import Mathlib.Analysis.Complex.Exponential
import Supplements.MathlibImports.AnalysisAndTactics
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

abbrev T0 : ℝ := Real.exp (-Real.exp (Real.exp 1))

section RM

open ReciprocityTheory.AnForm.A

end RM

end

end ReciprocityTheory.AnForm.P
