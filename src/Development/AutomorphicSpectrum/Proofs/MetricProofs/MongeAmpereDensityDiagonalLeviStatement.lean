module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityDiagonalLevi
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.monge_ampere_density_diagonal_levi : ∀ (e : ℕ) (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ), ContDiffAt ℝ 2 φ z → (∀ v, levi φ z v = ∑ q, dd q * ‖(M *ᵥ v) q‖ ^ 2) → maDens (fun _ => φ) z = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (∏ q, dd q) * ‖M.det‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi | exact GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi <;> assumption)
