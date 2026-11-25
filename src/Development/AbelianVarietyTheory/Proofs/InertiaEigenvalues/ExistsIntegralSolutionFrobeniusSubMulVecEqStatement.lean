module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralSolutionFrobeniusSubMulVecEq
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.exists_integral_solution_frobenius_sub_mulVec_eq : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b → ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  first | exact @GlobalTheory.PMonE.LangOnto.lang_onto | exact GlobalTheory.PMonE.LangOnto.lang_onto | (intros; apply GlobalTheory.PMonE.LangOnto.lang_onto <;> assumption)
