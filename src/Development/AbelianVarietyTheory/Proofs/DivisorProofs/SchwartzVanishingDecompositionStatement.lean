module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecomposition
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.schwartz_vanishing_decomposition : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ), f 0 = 0 → ∃ (n : ℕ) (L : Fin n → V →L[ℝ] ℝ) (h g : Fin n → SchwartzMap V ℂ),
      (∀ i x, g i x = (L i x : ℂ) * h i x) ∧ ∀ x, f x = ∑ i, g i x := by
  first | exact @GlobalTheory.SchwartzDiv.hadamard | exact GlobalTheory.SchwartzDiv.hadamard | (intros; apply GlobalTheory.SchwartzDiv.hadamard <;> assumption)
