module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLevelLatticeCompactOpen
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.adelic_level_lattice_compact_open : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ), 0 < N → IsCompact (latN F ι N : Set (ι → A F)) ∧ IsOpen (latN F ι N : Set (ι → A F)) ∧ ∀ a : ι → F, SB (indC N a) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.Lco.main | exact GlobalTheory.CompanionTheory.SW.ThW.Lco.main | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.Lco.main <;> assumption)
