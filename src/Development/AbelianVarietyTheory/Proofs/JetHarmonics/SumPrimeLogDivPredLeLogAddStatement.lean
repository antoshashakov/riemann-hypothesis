module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.sum_prime_log_div_pred_le_log_add : ∀ N : ℕ, ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 2.2 := by
  first | exact @GlobalTheory.PrimeLogSum.sum_log_div_pred_le | exact GlobalTheory.PrimeLogSum.sum_log_div_pred_le | (intros; apply GlobalTheory.PrimeLogSum.sum_log_div_pred_le <;> assumption)
