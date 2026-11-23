module

public import ReciprocityTheory.AnalyticForms.MaIntEmpty
import Supplements.MathlibImports.AnalysisAndTactics
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff Matrix

noncomputable section

theorem maDens_congr {D : ℕ} {F G : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, F k =ᶠ[𝓝 z] G k) : ReciprocityTheory.AnForm.maDens F z = ReciprocityTheory.AnForm.maDens G z := by
  have h2 : ∀ k, fderiv ℝ (fderiv ℝ (F k)) z = fderiv ℝ (fderiv ℝ (G k)) z :=
    fun k => ((h k).fderiv (𝕜 := ℝ)).fderiv_eq
  have h3 : (fun k => ReciprocityTheory.AnForm.hessC (F k) z) = fun k => ReciprocityTheory.AnForm.hessC (G k) z := by
    funext k
    ext i j
    dsimp only [ReciprocityTheory.AnForm.hessC]
    rw [h2 k]
  unfold ReciprocityTheory.AnForm.maDens
  rw [h3]

end

end GroundTheory.Heights₂.Heights
