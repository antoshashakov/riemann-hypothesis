module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CapGamma0LevelActsFreelyUpperHalfPlane
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.gamma1CapGamma0Level_acts_freely_upperHalfPlane : ∀ (N l : ℕ), 4 ≤ N → ∀ γ ∈ Gam N l, ∀ z ∈ Hs, mob (ofSL γ) z = z → γ = 1 := by
  first | exact @GlobalTheory.KZ.gam_free | exact GlobalTheory.KZ.gam_free | (intros; apply GlobalTheory.KZ.gam_free <;> assumption)
