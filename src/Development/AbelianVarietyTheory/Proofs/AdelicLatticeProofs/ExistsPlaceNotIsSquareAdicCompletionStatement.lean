module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotIsSquareAdicCompletion
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.exists_place_not_isSquare_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), u ≠ 0 → ¬ IsSquare u → ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  first | exact @GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion | exact GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion | (intros; apply GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion <;> assumption)
