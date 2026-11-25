module

public import Mathlib.NumberTheory.LocalField.Basic
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace GlobalTheory.CompanionTheory.LocalFieldValuationRing

theorem isFractionRing_integer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsFractionRing (ValuativeRel.valuation k).integer k :=
  (Valuation.integer.integers (ValuativeRel.valuation k)).isFractionRing

end GlobalTheory.CompanionTheory.LocalFieldValuationRing
