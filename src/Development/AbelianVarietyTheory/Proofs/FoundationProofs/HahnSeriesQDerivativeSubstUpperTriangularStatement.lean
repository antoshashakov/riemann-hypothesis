module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesQDerivativeSubstUpperTriangular
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

theorem _root_.GlobalTheory.T.hahnSeriesQDerivative_substUpperTriangular : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d → ∀ φ : HahnSeries ℚ Ω,
  qD (sub ε a b d φ) = HahnSeries.C (algebraMap ℚ Ω (a / d)) * sub ε a b d (qD φ) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.qD_sub | exact GlobalTheory.CyclotomicQExpansion.qD_sub | (intros; apply GlobalTheory.CyclotomicQExpansion.qD_sub <;> assumption)
