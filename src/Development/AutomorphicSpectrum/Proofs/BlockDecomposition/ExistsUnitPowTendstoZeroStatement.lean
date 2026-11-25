module

public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZero
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.exists_unit_pow_tendsto_zero' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∃ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) := by
  first | exact @GlobalTheory.CompanionTheory.LocalFieldPow.exists_unit_pow_tendsto_zero | exact GlobalTheory.CompanionTheory.LocalFieldPow.exists_unit_pow_tendsto_zero | (intros; apply GlobalTheory.CompanionTheory.LocalFieldPow.exists_unit_pow_tendsto_zero <;> assumption)
