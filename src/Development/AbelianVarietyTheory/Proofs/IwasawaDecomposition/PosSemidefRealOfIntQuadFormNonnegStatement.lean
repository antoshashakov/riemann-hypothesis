module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosSemidefRealOfIntQuadFormNonneg
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg : ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm → (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) → (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  first | exact @GlobalTheory.intSymm_posSemidef_real | exact GlobalTheory.intSymm_posSemidef_real | (intros; apply GlobalTheory.intSymm_posSemidef_real <;> assumption)
