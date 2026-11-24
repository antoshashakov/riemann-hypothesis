module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMulLowerTriangularOfDetN
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.exists_integral_unimodular_mul_lowerTriangular_of_det_ne_zero : ∀ (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F] [IsFractionRing V F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 → ∃ k : Matrix (Fin n) (Fin n) V, IsUnit k.det ∧ ∀ i j, i < j → (k.map (algebraMap V F) * A) i j = 0 := by
  first | exact @GlobalTheory.iwasawa_lowerTriangular_of_det | exact GlobalTheory.iwasawa_lowerTriangular_of_det | (intros; apply GlobalTheory.iwasawa_lowerTriangular_of_det <;> assumption)
