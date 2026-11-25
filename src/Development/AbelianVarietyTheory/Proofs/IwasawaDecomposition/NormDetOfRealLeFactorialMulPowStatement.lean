module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDetOfRealLeFactorialMulPow
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.norm_det_ofReal_le_factorial_mul_pow : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef → (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef → ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  first | exact @GlobalTheory.det_map_ofReal_norm_le | exact GlobalTheory.det_map_ofReal_norm_le | (intros; apply GlobalTheory.det_map_ofReal_norm_le <;> assumption)
