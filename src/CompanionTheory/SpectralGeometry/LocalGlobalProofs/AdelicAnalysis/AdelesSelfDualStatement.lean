module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesSelfDual
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.adeles_self_dual : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → NADual (A F) (fun x y => ψ (x * y)) (ENNReal.ofReal (kap F) • lf) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.SelfDual.finiteAdeles_selfDual | exact GlobalTheory.CompanionTheory.SW.Core.SelfDual.finiteAdeles_selfDual | (intros; apply GlobalTheory.CompanionTheory.SW.Core.SelfDual.finiteAdeles_selfDual <;> assumption)
