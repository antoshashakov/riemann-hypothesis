module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformRapidDecay
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField Complex MeasureTheory


theorem _root_.GlobalTheory.T.heckePhiFourierTransform_rapid_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ, ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_rapid_decay | exact GlobalTheory.HeckeTwo.hTrans_rapid_decay | (intros; apply GlobalTheory.HeckeTwo.hTrans_rapid_decay <;> assumption)
