module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingUnitAbsPowBounds
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.contracting_unit_abs_pow_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → 0 < nabs k t ∧ nabs k t < 1 ∧ ∀ d : ℕ, ‖((absPow k (d : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ d := by
  first | exact @GlobalTheory.CompanionTheory.TopNilp.nabs_absPow_of_tendsto_zero | exact GlobalTheory.CompanionTheory.TopNilp.nabs_absPow_of_tendsto_zero | (intros; apply GlobalTheory.CompanionTheory.TopNilp.nabs_absPow_of_tendsto_zero <;> assumption)
