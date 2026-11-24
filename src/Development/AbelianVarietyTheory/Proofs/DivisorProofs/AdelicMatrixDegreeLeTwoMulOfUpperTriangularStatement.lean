module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixDegreeLeTwoMulOfUpperTriangular
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.adelicMatrixDegree_le_two_mul_of_upperTriangular : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ 2 * b := by
  first | exact @GlobalTheory.Nef.deg_le_two_mul_of_triangular | exact GlobalTheory.Nef.deg_le_two_mul_of_triangular | (intros; apply GlobalTheory.Nef.deg_le_two_mul_of_triangular <;> assumption)
