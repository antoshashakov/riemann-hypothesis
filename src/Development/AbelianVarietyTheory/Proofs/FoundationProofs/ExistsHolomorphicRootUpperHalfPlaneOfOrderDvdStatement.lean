module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.Analysis.Meromorphic.Order
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneOfOrderDvd
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix GlobalTheory.KZ
open Filter Topology

theorem _root_.GlobalTheory.T.exists_holomorphic_root_upperHalfPlane_of_order_dvd : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs → (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := by
  first | exact @GlobalTheory.RootHs.rootHs | exact GlobalTheory.RootHs.rootHs | (intros; apply GlobalTheory.RootHs.rootHs <;> assumption)
