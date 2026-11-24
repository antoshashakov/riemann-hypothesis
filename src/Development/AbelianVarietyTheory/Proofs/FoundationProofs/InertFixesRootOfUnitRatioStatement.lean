module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatio
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.inert_apply_eq_of_pow_fixed_of_valuation_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (B : ValuationSubring Ω) (g : Ω ≃ₐ[K] Ω) (N : ℕ) (c θ : Ω),
  0 < N → B.valuation (N : Ω) = 1 → Inert B g → g c = c → c ≠ 0 → g (θ ^ N) = θ ^ N → B.valuation (θ ^ N / c ^ N) = 1 → g θ = θ := by
  first | exact @GlobalTheory.inert_fixes_root_of_unit_ratio | exact GlobalTheory.inert_fixes_root_of_unit_ratio | (intros; apply GlobalTheory.inert_fixes_root_of_unit_ratio <;> assumption)
