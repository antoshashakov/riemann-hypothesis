module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.Analysis.Meromorphic.Order
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnMeromorphicAtUpperHalfPlane
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix GlobalTheory.KZ
open Filter Topology

theorem _root_.GlobalTheory.T.an_meromorphicAt_upperHalfPlane : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K) (φ : ℂ → ℂ), X.an x = (φ : Mero) → ∀ τ : ℂ, τ ∈ Hs → MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := by
  first | exact @GlobalTheory.KZ.Tower.an_meromorphicAt | exact GlobalTheory.KZ.Tower.an_meromorphicAt | (intros; apply GlobalTheory.KZ.Tower.an_meromorphicAt <;> assumption)
