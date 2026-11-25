module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOne
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tensor_product_rank_le_one : ∀ {α : Type} [Fintype α] (M : α → Type) [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)], (∀ a, Module.rank ℂ (M a) ≤ 1) → Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one | exact GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one | (intros; apply GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one <;> assumption)
