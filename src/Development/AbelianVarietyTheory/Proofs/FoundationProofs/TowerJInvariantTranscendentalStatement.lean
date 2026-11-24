module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerJInvariantTranscendental
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.towerJInvariant_transcendental : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε), Transcendental Ω X.jK := by
  first | exact @GlobalTheory.KZ.Tower.jK_transcendental | exact GlobalTheory.KZ.Tower.jK_transcendental | (intros; apply GlobalTheory.KZ.Tower.jK_transcendental <;> assumption)
