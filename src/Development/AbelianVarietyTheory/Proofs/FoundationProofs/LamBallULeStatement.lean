module

public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULe
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.lam_ballU_le_ofReal_pow : ∀ (p q : ℕ) (lam : Measure (lieU p q)), IsOmegaLeb lam → ∀ r : ℝ, 0 < r → lam (ballU p q r) ≤ ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) := by
  first | exact @GlobalTheory.CartanInt.LamBall.lam_ballU_le | exact GlobalTheory.CartanInt.LamBall.lam_ballU_le | (intros; apply GlobalTheory.CartanInt.LamBall.lam_ballU_le <;> assumption)
