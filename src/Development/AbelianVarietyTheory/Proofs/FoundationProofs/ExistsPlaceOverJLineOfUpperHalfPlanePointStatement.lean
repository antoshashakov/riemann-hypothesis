module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Mathlib.Analysis.Meromorphic.Order
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceOverJLineOfUpperHalfPlanePoint
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix GlobalTheory.KZ
open Filter Topology

theorem _root_.GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ), τ ∈ Hs → ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 → ∀ φ : ℂ → ℂ, X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := by
  first | exact @GlobalTheory.KZ.ValAt.exists_place | exact GlobalTheory.KZ.ValAt.exists_place | (intros; apply GlobalTheory.KZ.ValAt.exists_place <;> assumption)
