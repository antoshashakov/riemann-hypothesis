module

public import GroundTheory.LocalFields.Different
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceMemMaximalIdealPowOfDifferentExponent
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.exists_trace_mem_maximalIdeal_pow_of_differentExponent : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (n : ℕ), (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * n ≤ differentExponent F M → ∀ z : 𝒪[M], ∃ w ∈ 𝓂[F] ^ n, ((w : 𝒪[F]) : F) = Algebra.trace F M (z : M) := by
  first | exact @GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent | exact GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent | (intros; apply GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent <;> assumption)
